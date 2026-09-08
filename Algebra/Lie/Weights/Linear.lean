/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lie modules with linear weights

Given a Lie module `M` over a nilpotent Lie algebra `L` with coefficients in `R`, one frequently
studies `M` via its weights. These are functions `χ : L → R` whose corresponding weight space
`LieModule.genWeightSpace M χ`, is non-trivial. If `L` is Abelian or if `R` has characteristic zero
(and `M` is finite-dimensional) then such `χ` are necessarily `R`-linear. However in general
non-linear weights do exist. For example if we take:
* `R`: the field with two elements (or indeed any perfect field of characteristic two),
* `L`: `sl₂` (this is nilpotent in characteristic two),
* `M`: the natural two-dimensional representation of `L`,

then there is a single weight and it is non-linear. (See remark following Proposition 9 of
chapter VII, §1.3 in [N. Bourbaki, Chapters 7--9](bourbaki1975b).)

We thus introduce a typeclass `LieModule.LinearWeights` to encode the fact that a Lie module does
have linear weights and provide typeclass instances in the two important cases that `L` is Abelian
or `R` has characteristic zero.

## Main definitions
* `LieModule.LinearWeights`: a typeclass encoding the fact that a given Lie module has linear
  weights, and furthermore that the weights vanish on the derived ideal.
* `LieModule.instLinearWeightsOfCharZero`: a typeclass instance encoding the fact that for an
  Abelian Lie algebra, the weights of any Lie module are linear.
* `LieModule.instLinearWeightsOfIsLieAbelian`: a typeclass instance encoding the fact that in
  characteristic zero, the weights of any finite-dimensional Lie module are linear.
* `LieModule.exists_forall_lie_eq_smul`: existence of simultaneous
  eigenvectors from existence of simultaneous generalized eigenvectors for Noetherian Lie modules
  with linear weights.

-/

@[expose] public section

open Set

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

/-- A typeclass encoding the fact that a given Lie module has linear weights, vanishing on the
derived ideal. -/
/-
**LieModule.LinearWeights** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieModule`。
形式化陈述：(R : Type u_2) →   (L : Type u_3) →     (M : Type u_4) →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] → [LieModule R L M] → [LieRing
.IsNilpotent L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass encoding the fact that a given Lie module has linear weights, vanish
ing on the
derived ideal.
-/
class LinearWeights [LieRing.IsNilpotent L] : Prop where
  map_add : ∀ χ : L → R, genWeightSpace M χ ≠ ⊥ → ∀ x y, χ (x + y) = χ x + χ y
  map_smul : ∀ χ : L → R, genWeightSpace M χ ≠ ⊥ → ∀ (t : R) x, χ (t • x) = t • χ x
  map_lie : ∀ χ : L → R, genWeightSpace M χ ≠ ⊥ → ∀ x y : L, χ ⁅x, y⁆ = 0

namespace Weight

variable [LieRing.IsNilpotent L] [LinearWeights R L M] (χ : Weight R L M)

/-- A weight of a Lie module, bundled as a linear map. -/
@[simps]
/-
**LieModule.Weight.toLinear** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Weight`。
形式化陈述：toLinear : L ->ₗ[R] R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weight of a Lie module, bundled as a linear map.
-/
def toLinear : L →ₗ[R] R where
  toFun := χ
  map_add' := LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smul' := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot
/-
**LieModule.Weight.instCoeLinearMap** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`
。
形式化陈述：instCoeLinearMap : CoeOut (Weight R L M) (L ->ₗ[R] R) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeLinearMap : CoeOut (Weight R L M) (L →ₗ[R] R) where
  coe := Weight.toLinear R L M
/-
**LieModule.Weight.instLinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weigh
t`。
形式化陈述：instLinearMapClass : LinearMapClass (Weight R L M) R L R where map_add χ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.LinearWeights.map_add`：∀ {R : Type u_2} {L : Type u_3} {M : Ty
pe u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   {in
st_3 : AddCommGroup M…
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `LieModule.LinearWeights.map_smul`：∀ {R : Type u_2} {L : Type u_3} {M : T
ype u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   {i
nst_3 : AddCommGroup M…
-/
instance instLinearMapClass : LinearMapClass (Weight R L M) R L R where
  map_add χ := LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smulₛₗ χ := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot

variable {R L M χ}

@[simp]
/-
**LieModule.Weight.apply_lie** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Weight`。
形式化陈述：apply_lie (x y : L) : χ ⁅x, y⁆ = 0
参数：x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.LinearWeights.map_lie`：∀ {R : Type u_2} {L : Type u_3} {M : Ty
pe u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   {in
st_3 : AddCommGroup M…
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
-/
lemma apply_lie (x y : L) :
    χ ⁅x, y⁆ = 0 :=
  LinearWeights.map_lie χ χ.genWeightSpace_ne_bot x y
/-
**LieModule.Weight.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : LieModule.LinearWeights R L M] {χ : LieMod
ule.Weight R L M},   ⇑(LieModule.Weight.toLinear R L M χ) = ⇑χ
参数：LieModule.Weight.toLinear R L M χ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_coe : (↑(χ : L →ₗ[R] R) : L → R) = (χ : L → R) := rfl
/-
**LieModule.Weight.coe_toLinear_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule
.Weight`。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [inst_8 : LieModule.LinearWeights R L M] {χ : LieMod
ule.Weight R L M},   LieModule.Weight.toLinear R L M χ = 0 ↔ χ.IsZero
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coe_toLinear_eq_zero_iff : (χ : L →ₗ[R] R) = 0 ↔ χ.IsZero :=
  ⟨fun h ↦ funext fun x ↦ LinearMap.congr_fun h x, fun h ↦ by ext; simp [h.eq]⟩
/-
**LieModule.Weight.coe_toLinear_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
.Weight`。
形式化陈述：coe_toLinear_ne_zero_iff : (χ : L ->ₗ[R] R) != 0 ↔ χ.IsNonZero
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_toLinear_ne_zero_iff : (χ : L →ₗ[R] R) ≠ 0 ↔ χ.IsNonZero := by simp

/-- The kernel of a weight of a Lie module with linear weights. -/
/-
**LieModule.Weight.ker** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieModule.Weight`。
形式化陈述：ker
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a weight of a Lie module with linear weights.
-/
abbrev ker := LinearMap.ker (χ : L →ₗ[R] R)

end Weight

attribute [local instance 100] LieRing.ofAssociativeRing

/-- For an Abelian Lie algebra, the weights of any Lie module are linear. -/
/-
**LieModule.instLinearWeightsOfIsLieAbelian** 是 Mathlib 中的一个实例，位于命名空间 `LieModule
`。
形式化陈述：instLinearWeightsOfIsLieAbelian [IsLieAbelian L] [IsDomain R] [Module.IsTo
rsionFree R M] : LinearWeights R L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_lie_eq`：commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
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
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用引理 `Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute`：map_add_of_i
Inf_genEigenspace_ne_bot_of_commute [IsDomain R] [IsTorsionFree R M] {L F : Type
*} [Add L] [FunLike F L (End R M)] [AddHomClass …
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.iInf_toSubmodule`：iInf_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨅ i, p i) : Submodule R M) = ⨅ i, (p i : Submodule R M)
· 使用引理 `Module.End.map_smul_of_iInf_genEigenspace_ne_bot`：map_smul_of_iInf_genEi
genspace_ne_bot [IsDomain R] [IsTorsionFree R M] {L F : Type*} [SMul R L] [FunLi
ke F L (End R M)] [MulActionHomClass F…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
For an Abelian Lie algebra, the weights of any Lie module are linear.
-/
instance instLinearWeightsOfIsLieAbelian [IsLieAbelian L] [IsDomain R] [Module.IsTorsionFree R M] :
    LinearWeights R L M :=
  have aux : ∀ (χ : L → R), genWeightSpace M χ ≠ ⊥ → ∀ (x y : L), χ (x + y) = χ x + χ y := by
    have h : ∀ x y, Commute (toEnd R L M x) (toEnd R L M y) := fun x y ↦ by
      rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, map_zero]
    intro χ hχ x y
    simp_rw [Ne, ← LieSubmodule.toSubmodule_inj, genWeightSpace, genWeightSpaceOf,
      LieSubmodule.iInf_toSubmodule, LieSubmodule.bot_toSubmodule] at hχ
    exact Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute
      (toEnd R L M).toLinearMap χ _ hχ h x y
  { map_add := aux
    map_smul := fun χ hχ t x ↦ by
      simp_rw [Ne, ← LieSubmodule.toSubmodule_inj, genWeightSpace, genWeightSpaceOf,
        LieSubmodule.iInf_toSubmodule, LieSubmodule.bot_toSubmodule] at hχ
      exact Module.End.map_smul_of_iInf_genEigenspace_ne_bot
        (toEnd R L M).toLinearMap χ _ hχ t x
    map_lie := fun χ hχ t x ↦ by
      rw [trivial_lie_zero, ← add_left_inj (χ 0), ← aux χ hχ, zero_add, zero_add] }

section FiniteDimensional

open Module

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
  [LieRing.IsNilpotent L]

/-
**LieModule.trace_comp_toEnd_genWeightSpace_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieMod
ule`。
形式化陈述：trace_comp_toEnd_genWeightSpace_eq (χ : L -> R) : LinearMap.trace R _ ∘ₗ (
toEnd R L (genWeightSpace M χ)).toLinearMap = finrank R (genWeightSpace M χ) • χ
参数：χ : L -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.trace_toEnd_genWeightSpace`：trace_toEnd_genWeightSpace [IsDoma
in R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M] (χ : L -> R
) (x : L) : trace R _ (toE…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_comp_toEnd_genWeightSpace_eq (χ : L → R) :
    LinearMap.trace R _ ∘ₗ (toEnd R L (genWeightSpace M χ)).toLinearMap =
    finrank R (genWeightSpace M χ) • χ := by
  ext x
  simp

variable {R L M} in
/-
**LieModule.zero_lt_finrank_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：zero_lt_finrank_genWeightSpace {χ : L -> R} (hχ : genWeightSpace M χ != ⊥)
 : 0 < finrank R (genWeightSpace M χ)
参数：hχ : genWeightSpace M χ != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Cardinal.instNontrivial`：Nontrivial Cardinal.{u}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `rank_pos_iff_nontrivial`：rank_pos_iff_nontrivial : 0 < Module.rank R M ↔
 Nontrivial M
· 使用定理 `LieSubmodule.instIsTorsionFreeSubtypeMem`：∀ {R : Type u} {L : Type v} {M
 : Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   
[inst_3 : _root_.Module R M] […
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `LieSubmodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot {N : LieSubmod
ule R L M} : Nontrivial N ↔ N != ⊥
-/
lemma zero_lt_finrank_genWeightSpace {χ : L → R} (hχ : genWeightSpace M χ ≠ ⊥) :
    0 < finrank R (genWeightSpace M χ) := by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ

/-- In characteristic zero, the weights of any finite-dimensional Lie module are linear and vanish
on the derived ideal. -/
/-
**LieModule.instLinearWeightsOfCharZero** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
形式化陈述：instLinearWeightsOfCharZero [CharZero R] : LinearWeights R L M where map_a
dd χ hχ x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Modul
e.Is…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `LieModule.zero_lt_finrank_genWeightSpace`：zero_lt_finrank_genWeightSpace
 {χ : L -> R} (hχ : genWeightSpace M χ != ⊥) : 0 < finrank R (genWeightSpace M χ
)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `LieModule.trace_comp_toEnd_genWeightSpace_eq`：trace_comp_toEnd_genWeight
Space_eq (χ : L -> R) : LinearMap.trace R _ ∘ₗ (toEnd R L (genWeightSpace M χ)).
toLinearMap = finrank R (genWeight…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LieHom.coe_toLinearMap`：coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->
ₗ[R] L₂) = f
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `Ring.lie_def`：lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.trace_mul_comm`：trace_mul_comm (f g : M ->ₗ[R] M) : trace R M 
(f * g) = trace R M (g * f)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
In characteristic zero, the weights of any finite-dimensional Lie module are lin
ear and vanish
on the derived ideal.
-/
instance instLinearWeightsOfCharZero [CharZero R] :
    LinearWeights R L M where
  map_add χ hχ x y := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne', smul_add, ← Pi.smul_apply,
      ← Pi.smul_apply, ← Pi.smul_apply, ← trace_comp_toEnd_genWeightSpace_eq, map_add]
  map_smul χ hχ t x := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne', smul_comm, ← Pi.smul_apply,
      ← Pi.smul_apply (finrank R _), ← trace_comp_toEnd_genWeightSpace_eq, map_smul]
  map_lie χ hχ x y := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne', nsmul_zero, ← Pi.smul_apply,
      ← trace_comp_toEnd_genWeightSpace_eq, LinearMap.comp_apply, LieHom.coe_toLinearMap,
      LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.trace_mul_comm, sub_self]

end FiniteDimensional

variable [LieRing.IsNilpotent L] (χ : L → R)

/-- A type synonym for the `χ`-weight space but with the action of `x : L`
on `m : genWeightSpace M χ`, shifted to act as `⁅x, m⁆ - χ x • m`. -/
/-
**LieModule.shiftedGenWeightSpace** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：shiftedGenWeightSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for the `χ`-weight space but with the action of `x : L`
on `m : genWeightSpace M χ`, shifted to act as `⁅x, m⁆ - χ x • m`.
-/
def shiftedGenWeightSpace := genWeightSpace M χ

namespace shiftedGenWeightSpace

/-
**LieModule.shiftedGenWeightSpace.aux** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.shift
edGenWeightSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux [h : Nontrivial (shiftedGenWeightSpace R L M χ)] : genWeightSpace M χ ≠ ⊥ :=
  (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h

variable [LinearWeights R L M]
/-
**LieModule.shiftedGenWeightSpace.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.shiftedG
enWeightSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRingModule L (shiftedGenWeightSpace R L M χ) where
  bracket x m := ⁅x, m⁆ - χ x • m
  add_lie x y m := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [add_lie, LinearWeights.map_add χ (aux R L M χ), add_smul]
    abel
  lie_add x m n := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [lie_add, smul_add]
    abel
  leibniz_lie x y m := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [lie_sub, lie_smul, lie_lie, LinearWeights.map_lie χ (aux R L M χ), zero_smul,
      sub_zero, smul_sub, smul_comm (χ x)]
    abel
/-
**LieModule.shiftedGenWeightSpace.coe_lie_shiftedGenWeightSpace_apply** 是 Mathli
b 中的一个定理，位于命名空间 `LieModule.shiftedGenWeightSpace`。
形式化陈述：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] (χ : L → R) [inst_8 : LieModule.LinearWeights R L M]
 (x : L)   (m : ↥(LieModule.shiftedGenWeightSpace R L M χ)), ↑⁅x, m⁆ = ⁅x, ↑m⁆ -
 χ x • ↑m
参数：R : Type u_2；L : Type u_3；M : Type u_4；χ : L → R；x : L；m : ↥(LieModule.shifte
dGenWeightSpace R L M χ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
@[simp] lemma coe_lie_shiftedGenWeightSpace_apply (x : L) (m : shiftedGenWeightSpace R L M χ) :
    letI : Bracket L (shiftedGenWeightSpace R L M χ) := LieRingModule.toBracket
    ⁅x, m⁆ = ⁅x, (m : M)⁆ - χ x • m :=
  rfl
/-
**LieModule.shiftedGenWeightSpace.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.shiftedG
enWeightSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule R L (shiftedGenWeightSpace R L M χ) where
  smul_lie t x m := by
    nontriviality shiftedGenWeightSpace R L M χ
    apply Subtype.ext
    rw [coe_lie_shiftedGenWeightSpace_apply]
    simp only [smul_lie, LinearWeights.map_smul χ (aux R L M χ), smul_assoc t, SetLike.val_smul]
    rw [← smul_sub]
    congr
  lie_smul t x m := by
    nontriviality shiftedGenWeightSpace R L M χ
    apply Subtype.ext
    rw [coe_lie_shiftedGenWeightSpace_apply]
    simp only [SetLike.val_smul, lie_smul]
    rw [smul_comm (χ x), ← smul_sub]
    congr

/-- Forgetting the action of `L`,
the spaces `genWeightSpace M χ` and `shiftedGenWeightSpace R L M χ` are equivalent. -/
/-
**LieModule.shiftedGenWeightSpace.shift** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.shi
ftedGenWeightSpace`。
形式化陈述：(R : Type u_2) →   (L : Type u_3) →     (M : Type u_4) →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] →                   [inst_6 : 
LieModule R L M] →                     [inst_7 : LieRing.IsNilpotent L] →       
                (χ : L → R) → ↥(LieModule.genWeightSpace M χ) ≃ₗ[R] ↥(LieModule.
shiftedGenWeightSpace R L M χ)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
Forgetting the action of `L`,
the spaces `genWeightSpace M χ` and `shiftedGenWeightSpace R L M χ` are equivale
nt.
-/
@[simps!] def shift : genWeightSpace M χ ≃ₗ[R] shiftedGenWeightSpace R L M χ := LinearEquiv.refl R _
/-
**LieModule.shiftedGenWeightSpace.toEnd_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.
shiftedGenWeightSpace`。
形式化陈述：toEnd_eq (x : L) : toEnd R L (shiftedGenWeightSpace R L M χ) x = (shift R 
L M χ).conj (toEnd R L (genWeightSpace M χ) x - χ x • LinearMap.id)
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieModule.shiftedGenWeightSpace.instSubtypeMemLieSubmodule`：∀ (R : Type 
u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [ins
t_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…

--- 原说明 ---
Forgetting the action of `L`,
the spaces `genWeightSpace M χ` and `shiftedGenWeightSpace R L M χ` are equivale
nt.
-/
lemma toEnd_eq (x : L) :
    toEnd R L (shiftedGenWeightSpace R L M χ) x =
    (shift R L M χ).conj (toEnd R L (genWeightSpace M χ) x - χ x • LinearMap.id) := by
  tauto

set_option backward.isDefEq.respectTransparency false in
/-- By Engel's theorem, if `M` is Noetherian, the shifted action `⁅x, m⁆ - χ x • m` makes the
`χ`-weight space into a nilpotent Lie module. -/
/-
**LieModule.shiftedGenWeightSpace.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.shiftedG
enWeightSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By Engel's theorem, if `M` is Noetherian, the shifted action `⁅x, m⁆ - χ x • m` 
makes the
`χ`-weight space into a nilpotent Lie module.
-/
instance [IsNoetherian R M] : IsNilpotent L (shiftedGenWeightSpace R L M χ) :=
  LieModule.isNilpotent_iff_forall'.mpr fun x ↦ isNilpotent_toEnd_sub_algebraMap M χ x

end shiftedGenWeightSpace

open shiftedGenWeightSpace in
/-- Given a Lie module `M` of a nilpotent Lie algebra `L` with coefficients in `R`,
if a function `χ : L → R` has a simultaneous generalized eigenvector for the action of `L`
then it has a simultaneous true eigenvector, provided `M` is Noetherian and has linear weights. -/
/-
**LieModule.exists_forall_lie_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：exists_forall_lie_eq_smul [LinearWeights R L M] [IsNoetherian R M] (χ : We
ight R L M) : exists m : M, m != 0 ∧ forall x : L, ⁅x, m⁆ = χ x • m
参数：χ : Weight R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot {N : LieSubmod
ule R L M} : Nontrivial N ↔ N != ⊥
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieModule.shiftedGenWeightSpace.instSubtypeMemLieSubmodule`：∀ (R : Type 
u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [ins
t_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `LieModule.nontrivial_max_triv_of_isNilpotent`：nontrivial_max_triv_of_isN
ilpotent [Nontrivial M] [IsNilpotent L M] : Nontrivial (maxTrivSubmodule R L M)
· 使用定理 `LieModule.shiftedGenWeightSpace.instIsNilpotentSubtypeMemLieSubmoduleOfI
sNoetherian`：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `LieModule.shiftedGenWeightSpace.coe_lie_shiftedGenWeightSpace_apply`：∀ (
R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRin
g L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…

--- 原说明 ---
Given a Lie module `M` of a nilpotent Lie algebra `L` with coefficients in `R`,
if a function `χ : L → R` has a simultaneous generalized eigenvector for the act
ion of `L`
then it has a simultaneous true eigenvector, provided `M` is Noetherian and has 
linear weights.
-/
lemma exists_forall_lie_eq_smul [LinearWeights R L M] [IsNoetherian R M] (χ : Weight R L M) :
    ∃ m : M, m ≠ 0 ∧ ∀ x : L, ⁅x, m⁆ = χ x • m := by
  replace hχ : Nontrivial (shiftedGenWeightSpace R L M χ) :=
    (LieSubmodule.nontrivial_iff_ne_bot R L M).mpr χ.genWeightSpace_ne_bot
  obtain ⟨⟨⟨m, _⟩, hm₁⟩, hm₂⟩ :=
    @exists_ne _ (nontrivial_max_triv_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)) 0
  simp_rw [mem_maxTrivSubmodule, Subtype.ext_iff,
    ZeroMemClass.coe_zero] at hm₁
  refine ⟨m, by simpa [LieSubmodule.mk_eq_zero] using hm₂, ?_⟩
  intro x
  have := hm₁ x
  rwa [coe_lie_shiftedGenWeightSpace_apply, sub_eq_zero] at this

/-- See `LieModule.exists_nontrivial_weightSpace_of_isSolvable` for the variant that
only assumes that `L` is solvable but additionally requires `k` to be of characteristic zero. -/
/-
**LieModule.exists_nontrivial_weightSpace_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名
空间 `LieModule`。
形式化陈述：exists_nontrivial_weightSpace_of_isNilpotent [Field k] [LieAlgebra k L] [M
odule k M] [Module.Finite k M] [LieModule k L M] [LinearWeights k L M] [IsTriang
ularizable k L M] [Nontrivial M] : exists χ : Module.Dual k L, Nontrivial (weigh
tSpace M χ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用定理 `LieSubmodule.instNontrivial`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _ro
ot_.Module R M] […
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top'`：iSup_genWeightSpace_eq_top' [IsTr
iangularizable K L M] : ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤
· 使用引理 `LieModule.exists_forall_lie_eq_smul`：exists_forall_lie_eq_smul [LinearWe
ights R L M] [IsNoetherian R M] (χ : Weight R L M) : exists m : M, m != 0 ∧ fora
ll x : L, ⁅x, m⁆ = χ x • …
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
See `LieModule.exists_nontrivial_weightSpace_of_isSolvable` for the variant that
only assumes that `L` is solvable but additionally requires `k` to be of charact
eristic zero.
-/
lemma exists_nontrivial_weightSpace_of_isNilpotent [Field k] [LieAlgebra k L] [Module k M]
    [Module.Finite k M] [LieModule k L M] [LinearWeights k L M]
    [IsTriangularizable k L M] [Nontrivial M] :
    ∃ χ : Module.Dual k L, Nontrivial (weightSpace M χ) := by
  obtain ⟨χ⟩ : Nonempty (Weight k L M) := by
    by_contra! contra
    simpa only [iSup_of_empty, bot_ne_top] using LieModule.iSup_genWeightSpace_eq_top' k L M
  obtain ⟨m, hm₀, hm⟩ := exists_forall_lie_eq_smul k L M χ
  simp only [LieSubmodule.nontrivial_iff_ne_bot, LieSubmodule.eq_bot_iff, ne_eq, not_forall]
  exact ⟨χ.toLinear, m, by simpa [mem_weightSpace], hm₀⟩

end LieModule

