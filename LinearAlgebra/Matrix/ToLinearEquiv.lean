/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Matrices and linear equivalences

This file gives the map `Matrix.toLinearEquiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

* `Matrix.toLinearEquiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

* `Matrix.exists_mulVec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear equivalence, linear isomorphism, determinant, inverse

-/

@[expose] public section

open Module

variable {n : Type*} [Fintype n]

namespace Matrix

section LinearEquiv

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section ToLinearEquiv'

variable [DecidableEq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `Matrix.toLinearEquiv` for the same map on arbitrary modules.
-/
/-
**Matrix.toLinearEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toLinearEquiv' (P : Matrix n n R) (_ : Invertible P) : (n -> R) ≃ₗ[R] n ->
 R
参数：P : Matrix n n R；_ : Invertible P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invertible matrix yields a linear equivalence from the free module to itself.

See `Matrix.toLinearEquiv` for the same map on arbitrary modules.
-/
def toLinearEquiv' (P : Matrix n n R) (_ : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  GeneralLinearGroup.generalLinearEquiv _ _ <|
    Matrix.GeneralLinearGroup.toLin <| unitOfInvertible P

@[simp]
/-
**Matrix.toLinearEquiv'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] {R : Type u_2} [inst_1 : CommRing R] [
inst_2 : DecidableEq n] (P : Matrix n n R)   (h : Invertible P), ↑(P.toLinearEqu
iv' h) = Matrix.toLin' P
参数：P : Matrix n n R；h : Invertible P；P.toLinearEquiv' h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv'_apply (P : Matrix n n R) (h : Invertible P) :
    (P.toLinearEquiv' h : Module.End R (n → R)) = Matrix.toLin' P :=
  rfl

@[simp]
/-
**Matrix.toLinearEquiv'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] {R : Type u_2} [inst_1 : CommRing R] [
inst_2 : DecidableEq n] (P : Matrix n n R)   (h : Invertible P), ↑(P.toLinearEqu
iv' h).symm = Matrix.toLin' ⅟P
参数：P : Matrix n n R；h : Invertible P；P.toLinearEquiv' h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n → R)) = Matrix.toLin' (⅟P) :=
  rfl

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

/-- Given `hA : IsUnit A.det` and `b : Basis R b`, `A.toLinearEquiv b hA` is
the `LinearEquiv` arising from `toLin b b A`.

See `Matrix.toLinearEquiv'` for this result on `n → R`.
-/
@[simps apply]
/-
**Matrix.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : M ≃
ₗ[R] M where __
参数：A : Matrix n n R；hA : IsUnit A.det。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Given `hA : IsUnit A.det` and `b : Basis R b`, `A.toLinearEquiv b hA` is
the `LinearEquiv` arising from `toLin b b A`.

See `Matrix.toLinearEquiv'` for this result on `n → R`.
-/
noncomputable def toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    M ≃ₗ[R] M where
  __ := toLin b b A
  toFun := toLin b b A
  invFun := toLin b b A⁻¹
  left_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA,
      toLin_one, LinearMap.id_apply]
  right_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.mul_nonsing_inv _ hA,
      toLin_one, LinearMap.id_apply]
/-
**Matrix.ker_toLin_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : 
LinearMap.ker (toLin b b A) = ⊥
参数：A : Matrix n n R；hA : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.ker (toLin b b A) = ⊥ :=
  ker_eq_bot.mpr (toLinearEquiv b A hA).injective
/-
**Matrix.range_toLin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) 
: LinearMap.range (toLin b b A) = ⊤
参数：A : Matrix n n R；hA : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
theorem range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.range (toLin b b A) = ⊤ :=
  range_eq_top.mpr (toLinearEquiv b A hA).surjective

end ToLinearEquiv

section Nondegenerate

open Matrix

/-- This holds for all integral domains (see `Matrix.exists_mulVec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
/-
**Matrix.exists_mulVec_eq_zero_iff_aux** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This holds for all integral domains (see `Matrix.exists_mulVec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first.
-/
private theorem exists_mulVec_eq_zero_iff_aux {K : Type*} [DecidableEq n] [Field K]
    {M : Matrix n n K} : (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0 := by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mulVec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective (Matrix.toLin' M) := by
      simpa only [← LinearMap.ker_eq_bot, ker_toLin'_eq_bot_iff, not_imp_not] using h
    have : M * (LinearEquiv.ofInjectiveEndo _ this).symm.toMatrix' = 1 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix', LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this
/-
**Matrix.exists_mulVec_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_mulVec_eq_zero_iff' {A : Type*} (K : Type*) [DecidableEq n] [CommRing A]
    [Nontrivial A] [Field K] [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} :
    (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0 := by
  have : (∃ v ≠ 0, (algebraMap A K).mapMatrix M *ᵥ v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det, IsFractionRing.to_map_eq_zero_iff] at this
  refine Iff.trans ?_ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => ?_) hv, ?_⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine (RingHom.map_mulVec _ _ _ i).symm.trans ?_
      rw [mul_eq, Pi.zero_apply, map_zero, Pi.zero_apply]
  · let := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => ?_) hv, ?_⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf, Subtype.coe_mk, Pi.zero_apply, map_zero, Algebra.smul_def, mul_eq_zero,
        IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine IsFractionRing.injective A K ?_
      calc
        algebraMap A K ((M *ᵥ (fun i : n => f (v i) _)) i) =
            ((algebraMap A K).mapMatrix M *ᵥ algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]

variable {A : Type*} [CommRing A] [IsDomain A] {M N : Matrix n n A}
/-
**Matrix.exists_mulVec_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exists_mulVec_eq_zero_iff [DecidableEq n] : (exists v != 0, M *ᵥ v = 0) ↔ 
M.det = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.ToLinearEquiv.0.Matrix.exists_mulV
ec_eq_zero_iff'`：∀ {n : Type u_1} [inst : Fintype n] {A : Type u_4} (K : Type u_
5) [inst_1 : DecidableEq n] [inst_2 : CommRing A]   [Nontrivial A] [inst_4 : …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem exists_mulVec_eq_zero_iff [DecidableEq n] : (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0 :=
  exists_mulVec_eq_zero_iff' (FractionRing A)
/-
**Matrix.exists_vecMul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exists_vecMul_eq_zero_iff [DecidableEq n] : (exists v != 0, v ᵥ* M = 0) ↔ 
M.det = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.exists_mulVec_eq_zero_iff`：exists_mulVec_eq_zero_iff [DecidableEq
 n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
-/
theorem exists_vecMul_eq_zero_iff [DecidableEq n] : (∃ v ≠ 0, v ᵥ* M = 0) ↔ M.det = 0 := by
  simpa only [← M.det_transpose, ← mulVec_transpose] using exists_mulVec_eq_zero_iff
/-
**Matrix.nondegenerate_iff_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nondegenerate_iff_det_ne_zero [DecidableEq n] : Nondegenerate M ↔ M.det !=
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nondegenerate_iff_det_ne_zero [DecidableEq n] : Nondegenerate M ↔ M.det ≠ 0 := by
  grind [nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero, exists_mulVec_eq_zero_iff,
    exists_vecMul_eq_zero_iff]
/-
**Matrix.separatingLeft_iff_det_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：separatingLeft_iff_det_ne_zero [DecidableEq n] : SeparatingLeft M ↔ M.det 
!= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma separatingLeft_iff_det_ne_zero [DecidableEq n] : SeparatingLeft M ↔ M.det ≠ 0 := by
  grind [separatingLeft_iff_forall_vecMul_eq_zero, exists_vecMul_eq_zero_iff]
/-
**Matrix.separatingRight_iff_det_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：separatingRight_iff_det_ne_zero [DecidableEq n] : SeparatingRight M ↔ M.de
t != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma separatingRight_iff_det_ne_zero [DecidableEq n] : SeparatingRight M ↔ M.det ≠ 0 := by
  grind [separatingRight_iff_forall_mulVec_eq_zero, exists_mulVec_eq_zero_iff]

omit [Fintype n] in
/-
**Matrix.nondegenerate_iff_separatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nondegenerate_iff_separatingLeft [Finite n] : M.Nondegenerate ↔ M.Separati
ngLeft
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用引理 `Matrix.separatingLeft_iff_det_ne_zero`：separatingLeft_iff_det_ne_zero [D
ecidableEq n] : SeparatingLeft M ↔ M.det != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nondegenerate_iff_separatingLeft [Finite n] : M.Nondegenerate ↔ M.SeparatingLeft := by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero, separatingLeft_iff_det_ne_zero]

alias ⟨_, SeparatingLeft.nondegenerate⟩ := nondegenerate_iff_separatingLeft

omit [Fintype n] in
/-
**Matrix.nondegenerate_iff_separatingRight** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nondegenerate_iff_separatingRight [Finite n] : M.Nondegenerate ↔ M.Separat
ingRight
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用引理 `Matrix.separatingRight_iff_det_ne_zero`：separatingRight_iff_det_ne_zero 
[DecidableEq n] : SeparatingRight M ↔ M.det != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nondegenerate_iff_separatingRight [Finite n] : M.Nondegenerate ↔ M.SeparatingRight := by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero, separatingRight_iff_det_ne_zero]

alias ⟨_, SeparatingRight.nondegenerate⟩ := nondegenerate_iff_separatingRight

omit [Fintype n] in
/-
**Matrix.separatingLeft_iff_separatingRight** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：separatingLeft_iff_separatingRight [Finite n] : M.SeparatingLeft ↔ M.Separ
atingRight
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.nondegenerate_iff_separatingLeft`：nondegenerate_iff_separatingLef
t [Finite n] : M.Nondegenerate ↔ M.SeparatingLeft
· 使用定理 `Matrix.nondegenerate_iff_separatingRight`：nondegenerate_iff_separatingRi
ght [Finite n] : M.Nondegenerate ↔ M.SeparatingRight
-/
theorem separatingLeft_iff_separatingRight [Finite n] : M.SeparatingLeft ↔ M.SeparatingRight :=
  nondegenerate_iff_separatingLeft.symm.trans nondegenerate_iff_separatingRight

alias ⟨SeparatingLeft.separatingRight, SeparatingRight.separatingLeft⟩ :=
  separatingLeft_iff_separatingRight
/-
**Matrix.Nondegenerate.mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nondegene
rate`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] {A : Type u_4} [inst_1 : CommRing A] [
IsDomain A] {M N : Matrix n n A},   N.Nondegenerate → ((M * N).Nondegenerate ↔ M
.Nondegenerate)
参数：(M * N).Nondegenerate ↔ M.Nondegenerate。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `mul_ne_zero_iff_right`：mul_ne_zero_iff_right (hb : b != 0) : a * b != 0 
↔ a != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem Nondegenerate.mul_iff_right (h : N.Nondegenerate) :
    (M * N).Nondegenerate ↔ M.Nondegenerate := by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_right h
/-
**Matrix.Nondegenerate.mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nondegener
ate`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] {A : Type u_4} [inst_1 : CommRing A] [
IsDomain A] {M N : Matrix n n A},   M.Nondegenerate → ((M * N).Nondegenerate ↔ N
.Nondegenerate)
参数：(M * N).Nondegenerate ↔ N.Nondegenerate。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `mul_ne_zero_iff_left`：mul_ne_zero_iff_left (ha : a != 0) : a * b != 0 ↔ 
b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem Nondegenerate.mul_iff_left (h : M.Nondegenerate) :
    (M * N).Nondegenerate ↔ N.Nondegenerate := by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_left h

omit [Fintype n] in
/-
**Matrix.Nondegenerate.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nondegenerate`
。
形式化陈述：∀ {n : Type u_1} {A : Type u_4} [inst : CommRing A] [IsDomain A] {M : Matr
ix n n A} [inst_2 : Finite n] {t : A},   t ≠ 0 → ((t • M).Nondegenerate ↔ M.Nond
egenerate)
参数：(t • M).Nondegenerate ↔ M.Nondegenerate。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Matrix.nondegenerate_def`：nondegenerate_def [Fintype m] [Fintype n] : M.
Nondegenerate ↔ (forall v, (forall w, v ⬝ᵥ M *ᵥ w = 0) -> v = 0) ∧ (forall w, (f
orall v, v ⬝ᵥ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matrix.smul_mulVec`：smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarT
ower R α α] (b : R) (M : Matrix m n α) (v : n -> α) : (b • M) *ᵥ v = b • M *ᵥ v
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `dotProduct_smul`：dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m 
-> α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mul_eq_zero_iff_left`：mul_eq_zero_iff_left (ha : a != 0) : a * b = 0 ↔ b
 = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nondegenerate.smul_iff [Finite n] {t : A} (h : t ≠ 0) :
    (t • M).Nondegenerate ↔ M.Nondegenerate := by
  have := Fintype.ofFinite
  rw [nondegenerate_def, nondegenerate_def]
  simp [smul_mulVec, mul_eq_zero_iff_left h]

alias ⟨Nondegenerate.det_ne_zero, Nondegenerate.of_det_ne_zero⟩ := nondegenerate_iff_det_ne_zero

end Nondegenerate

end LinearEquiv

section Determinant

/-- A matrix whose nondiagonal entries are negative with the sum of the entries of each
column positive has nonzero determinant. -/
/-
**Matrix.det_ne_zero_of_sum_col_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：det_ne_zero_of_sum_col_pos [DecidableEq n] {S : Type*} [CommRing S] [Linea
rOrder S] [IsStrictOrderedRing S] {A : Matrix n n S} (h1 : Pairwise fun i j => A
 i j < 0) (h2 : forall j, 0 < ∑ i, A i j) : A.det != 0
参数：h1 : Pairwise fun i j => A i j < 0；h2 : forall j, 0 < ∑ i, A i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.coe_det_isEmpty`：coe_det_isEmpty [IsEmpty n] : (det : Matrix n n 
R -> R) = Function.const _ 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.exists_vecMul_eq_zero_iff`：exists_vecMul_eq_zero_iff [DecidableEq
 n] : (exists v != 0, v ᵥ* M = 0) ↔ M.det = 0
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
A matrix whose nondiagonal entries are negative with the sum of the entries of e
ach
column positive has nonzero determinant.
-/
lemma det_ne_zero_of_sum_col_pos [DecidableEq n]
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {A : Matrix n n S} (h1 : Pairwise fun i j => A i j < 0) (h2 : ∀ j, 0 < ∑ i, A i j) :
    A.det ≠ 0 := by
  cases isEmpty_or_nonempty n
  · simp
  · contrapose! h2
    obtain ⟨v, ⟨h_vnz, h_vA⟩⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h2
    wlog h_sup : 0 < Finset.sup' Finset.univ Finset.univ_nonempty v
    · refine this h1 inferInstance h2 (-1 • v) (by simp [*]) ?_ ?_
      · rw [Matrix.smul_vecMul, h_vA, smul_zero]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h_vnz
        simp_rw [Finset.lt_sup'_iff, Finset.mem_univ, true_and] at h_sup ⊢
        simp_rw [not_exists, not_lt] at h_sup
        refine ⟨i, ?_⟩
        rw [Pi.smul_apply, neg_smul, one_smul, Left.neg_pos_iff]
        exact Ne.lt_of_le hi (h_sup i)
    · obtain ⟨j₀, -, h_j₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
      refine ⟨j₀, ?_⟩
      rw [← mul_le_mul_iff_right₀ (h_j₀ ▸ h_sup), Finset.mul_sum, mul_zero]
      rw [show 0 = ∑ i, v i * A i j₀ from (congrFun h_vA j₀).symm]
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h : i = j₀
      · rw [h]
      · exact (mul_le_mul_right_of_neg (h1 h)).mpr (h_j₀ ▸ Finset.le_sup' v hi)

/-- A matrix whose nondiagonal entries are negative with the sum of the entries of each
row positive has nonzero determinant. -/
/-
**Matrix.det_ne_zero_of_sum_row_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：det_ne_zero_of_sum_row_pos [DecidableEq n] {S : Type*} [CommRing S] [Linea
rOrder S] [IsStrictOrderedRing S] {A : Matrix n n S} (h1 : Pairwise fun i j => A
 i j < 0) (h2 : forall i, 0 < ∑ j, A i j) : A.det != 0
参数：h1 : Pairwise fun i j => A i j < 0；h2 : forall i, 0 < ∑ j, A i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用引理 `Matrix.det_ne_zero_of_sum_col_pos`：det_ne_zero_of_sum_col_pos [Decidable
Eq n] {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] {A : Matr
ix n n S} (h1 : Pairwis…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
A matrix whose nondiagonal entries are negative with the sum of the entries of e
ach
row positive has nonzero determinant.
-/
lemma det_ne_zero_of_sum_row_pos [DecidableEq n]
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {A : Matrix n n S} (h1 : Pairwise fun i j => A i j < 0) (h2 : ∀ i, 0 < ∑ j, A i j) :
    A.det ≠ 0 := by
  rw [← Matrix.det_transpose]
  refine det_ne_zero_of_sum_col_pos ?_ ?_
  · simp_rw [Matrix.transpose_apply]
    exact fun i j h => h1 h.symm
  · simp_rw [Matrix.transpose_apply]
    exact h2

end Determinant

end Matrix

