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

/--
Definition of `LinearWeights` / `LinearWeights` 的定义

English:
class LinearWeights
  parameters: [LieRing.IsNilpotent L]
  axioms and operations (3):
    - map_add : forall χ : L -> R, genWeightSpace M χ != ⊥ -> forall x y, χ (x + y) = χ x + χ y
    - map_smul : forall χ : L -> R, genWeightSpace M χ != ⊥ -> forall (t : R) x, χ (t • x) = t • χ x
    - map_lie : forall χ : L -> R, genWeightSpace M χ != ⊥ -> forall x y : L, χ ⁅x, y⁆ = 0

中文:
类 LinearWeights
  参数: [Lie环.是幂零 L]
  公理与运算 (3 个):
    - map_add : 对任意 χ : L -> R, genWeightSpace M χ != ⊥ -> 对任意 x y, χ (x + y) = χ x + χ y
    - map_smul : 对任意 χ : L -> R, genWeightSpace M χ != ⊥ -> 对任意 (t : R) x, χ (t • x) = t • χ x
    - map_lie : 对任意 χ : L -> R, genWeightSpace M χ != ⊥ -> 对任意 x y : L, χ ⁅x, y⁆ = 0
-/
class LinearWeights [LieRing.IsNilpotent L] : Prop where
  map_add : forall χ : L -> R, genWeightSpace M χ != ⊥ -> forall x y, χ (x + y) = χ x + χ y
  map_smul : forall χ : L -> R, genWeightSpace M χ != ⊥ -> forall (t : R) x, χ (t • x) = t • χ x
  map_lie : forall χ : L -> R, genWeightSpace M χ != ⊥ -> forall x y : L, χ ⁅x, y⁆ = 0

namespace Weight

variable [LieRing.IsNilpotent L] [LinearWeights R L M] (χ : Weight R L M)

/-- A weight of a Lie module, bundled as a linear map. -/
@[simps]
/--
Definition of `toLinear` / `toLinear` 的定义

English:
definition toLinear
  signature: : L ->ₗ[R] R where
  body: χ
  map_add' := LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smul' := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot

中文:
定义 toLinear
  签名: : L ->ₗ[R] R where
  定义体: χ
  map_add' := LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smul' := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot
-/
def toLinear : L ->ₗ[R] R where
  toFun := χ
  map_add' := LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smul' := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot

/--
Instance `instCoeLinearMap` / 实例 `instCoeLinearMap`

English:
instance instCoeLinearMap
  signature: : CoeOut (Weight R L M) (L ->ₗ[R] R) where
  body: Weight.toLinear R L M

中文:
实例 instCoeLinearMap
  签名: : CoeOut (Weight R L M) (L ->ₗ[R] R) where
  定义体: Weight.toLinear R L M

Depends on / 依赖: Weight, Weight.toLinear, toLinear
-/
instance instCoeLinearMap : CoeOut (Weight R L M) (L ->ₗ[R] R) where
  coe := Weight.toLinear R L M

/--
Instance `instLinearMapClass` / 实例 `instLinearMapClass`

English:
instance instLinearMapClass
  signature: : LinearMapClass (Weight R L M) R L R where
  body: LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smulₛₗ χ := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot

中文:
实例 instLinearMapClass
  签名: : 线性映射类 (Weight R L M) R L R where
  定义体: LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smulₛₗ χ := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot

Depends on / 依赖: LinearWeights, LinearWeights.map_add, genWeightSpace_ne_bot, map_add
-/
instance instLinearMapClass : LinearMapClass (Weight R L M) R L R where
  map_add χ := LinearWeights.map_add χ χ.genWeightSpace_ne_bot
  map_smulₛₗ χ := LinearWeights.map_smul χ χ.genWeightSpace_ne_bot

variable {R L M χ}

@[simp]
/--
lemma `apply_lie` / 引理 `apply_lie`

English:
lemma apply_lie
  given: (x y : L)
  proof: LinearWeights.map_lie χ χ.genWeightSpace_ne_bot x y

中文:
引理 apply_lie
  条件: (x y : L)
  证明: LinearWeights.map_lie χ χ.genWeightSpace_ne_bot x y

Depends on / 依赖: LinearWeights, LinearWeights.map_lie, genWeightSpace_ne_bot, map_lie
-/
lemma apply_lie (x y : L) :
    χ ⁅x, y⁆ = 0 :=
  LinearWeights.map_lie χ χ.genWeightSpace_ne_bot x y

/--
lemma `coe_coe` / 引理 `coe_coe`

English:
lemma coe_coe
  statement: (↑(χ : L ->ₗ[R] R) : L -> R) = (χ : L -> R)
  proof: rfl

中文:
引理 coe_coe
  结论: (↑(χ : L ->ₗ[R] R) : L -> R) = (χ : L -> R)
  证明: rfl
-/
@[simp] lemma coe_coe : (↑(χ : L ->ₗ[R] R) : L -> R) = (χ : L -> R) := rfl

/--
lemma `coe_toLinear_eq_zero_iff` / 引理 `coe_toLinear_eq_zero_iff`

English:
lemma coe_toLinear_eq_zero_iff
  statement: (χ : L ->ₗ[R] R) = 0 ↔ χ.IsZero
  proof: ⟨fun h => funext fun x => LinearMap.congr_fun h x, fun h => by ext; simp [h.eq]⟩

中文:
引理 coe_toLinear_eq_zero_iff
  结论: (χ : L ->ₗ[R] R) = 0 ↔ χ.是零
  证明: ⟨fun h => funext fun x => LinearMap.congr_fun h x, fun h => by ext; simp [h.eq]⟩
-/
@[simp] lemma coe_toLinear_eq_zero_iff : (χ : L ->ₗ[R] R) = 0 ↔ χ.IsZero :=
  ⟨fun h => funext fun x => LinearMap.congr_fun h x, fun h => by ext; simp [h.eq]⟩

/--
lemma `coe_toLinear_ne_zero_iff` / 引理 `coe_toLinear_ne_zero_iff`

English:
lemma coe_toLinear_ne_zero_iff
  statement: (χ : L ->ₗ[R] R) != 0 ↔ χ.IsNonZero
  proof: by simp

中文:
引理 coe_toLinear_ne_zero_iff
  结论: (χ : L ->ₗ[R] R) != 0 ↔ χ.IsNonZero
  证明: by simp
-/
lemma coe_toLinear_ne_zero_iff : (χ : L ->ₗ[R] R) != 0 ↔ χ.IsNonZero := by simp

/--
Definition of `ker` / `ker` 的定义

English:
abbreviation ker
  body: LinearMap.ker (χ : L ->ₗ[R] R)

中文:
缩写 ker
  定义体: LinearMap.ker (χ : L ->ₗ[R] R)

Depends on / 依赖: LinearMap, LinearMap.ker
-/
abbrev ker := LinearMap.ker (χ : L ->ₗ[R] R)

end Weight

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Instance `instLinearWeightsOfIsLieAbelian` / 实例 `instLinearWeightsOfIsLieAbelian`

English:
instance instLinearWeightsOfIsLieAbelian
  signature: [IsLieAbelian L] [IsDomain R] [Module.IsTorsionFree R M]
  body: have aux : forall (χ : L -> R), genWeightSpace M χ != ⊥ -> forall (x y : L), χ (x + y) = χ x + χ y := by
    have h : forall x y, Commute (toEnd R L M x) (toEnd R L M y) := fun x y => by
      rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero]
    intro χ hχ x y
   

中文:
实例 instLinearWeightsOfIsLieAbelian
  签名: [IsLieAbelian L] [是整环 R] [模.是无挠 R M]
  定义体: have aux : forall (χ : L -> R), genWeightSpace M χ != ⊥ -> forall (x y : L), χ (x + y) = χ x + χ y := by
    have h : forall x y, Commute (toEnd R L M x) (toEnd R L M y) := fun x y => by
      rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero]
    intro χ hχ x y
   

Depends on / 依赖: Commute, LieHom, LieHom.map_lie, LieSubmodule, LieSubmodule.bot_toSubmodule, LieSubmodule.iInf_toSubmodule, LieSubmodule.toSubmodule_inj, Module, Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute, bot_toSubmodule, commute_iff_lie_eq, genWeightSpace, genWeightSpaceOf, iInf_toSubmodule, map_add_of_iInf_genEigenspace_ne_bot_of_commute, map_lie, map_zero, simp_rw, toSubmodule_inj, trivial_lie_zero
-/
instance instLinearWeightsOfIsLieAbelian [IsLieAbelian L] [IsDomain R] [Module.IsTorsionFree R M] :
    LinearWeights R L M :=
  have aux : forall (χ : L -> R), genWeightSpace M χ != ⊥ -> forall (x y : L), χ (x + y) = χ x + χ y := by
    have h : forall x y, Commute (toEnd R L M x) (toEnd R L M y) := fun x y => by
      rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero]
    intro χ hχ x y
    simp_rw [Ne, ← LieSubmodule.toSubmodule_inj, genWeightSpace, genWeightSpaceOf,
      LieSubmodule.iInf_toSubmodule, LieSubmodule.bot_toSubmodule] at hχ
    exact Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute
      (toEnd R L M).toLinearMap χ _ hχ h x y
  { map_add := aux
    map_smul := fun χ hχ t x => by
      simp_rw [Ne, ← LieSubmodule.toSubmodule_inj, genWeightSpace, genWeightSpaceOf,
        LieSubmodule.iInf_toSubmodule, LieSubmodule.bot_toSubmodule] at hχ
      exact Module.End.map_smul_of_iInf_genEigenspace_ne_bot
        (toEnd R L M).toLinearMap χ _ hχ t x
    map_lie := fun χ hχ t x => by
      rw [trivial_lie_zero]; rw [← add_left_inj (χ 0)]; rw [← aux χ hχ]; rw [zero_add]; rw [zero_add] }

section FiniteDimensional

open Module

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
  [LieRing.IsNilpotent L]

/--
lemma `trace_comp_toEnd_genWeightSpace_eq` / 引理 `trace_comp_toEnd_genWeightSpace_eq`

English:
lemma trace_comp_toEnd_genWeightSpace_eq
  given: (χ : L -> R)
  proof: by
  ext x
  simp

中文:
引理 trace_comp_toEnd_genWeightSpace_eq
  条件: (χ : L -> R)
  证明: by
  ext x
  simp
-/
lemma trace_comp_toEnd_genWeightSpace_eq (χ : L -> R) :
    LinearMap.trace R _ ∘ₗ (toEnd R L (genWeightSpace M χ)).toLinearMap =
    finrank R (genWeightSpace M χ) • χ := by
  ext x
  simp

variable {R L M} in
/--
lemma `zero_lt_finrank_genWeightSpace` / 引理 `zero_lt_finrank_genWeightSpace`

English:
lemma zero_lt_finrank_genWeightSpace
  given: {χ : L -> R} (hχ : genWeightSpace M χ != ⊥)
  proof: by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ

中文:
引理 zero_lt_finrank_genWeightSpace
  条件: {χ : L -> R} (hχ : genWeightSpace M χ != ⊥)
  证明: by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ

Depends on / 依赖: LieSubmodule, LieSubmodule.nontrivial_iff_ne_bot, Nat.cast_pos, cast_pos, finrank_eq_rank, nontrivial_iff_ne_bot, rank_pos_iff_nontrivial
-/
lemma zero_lt_finrank_genWeightSpace {χ : L -> R} (hχ : genWeightSpace M χ != ⊥) :
    0 < finrank R (genWeightSpace M χ) := by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ

/--
Instance `instLinearWeightsOfCharZero` / 实例 `instLinearWeightsOfCharZero`

English:
instance instLinearWeightsOfCharZero
  signature: [CharZero R]
  body: by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; rw [smul_add]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]; rw [← trace_comp_toEnd_genWeightSpace_eq]; rw [map_add]
  map_smul χ hχ t x := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; 

中文:
实例 instLinearWeightsOfCharZero
  签名: [特征零 R]
  定义体: by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; rw [smul_add]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]; rw [← trace_comp_toEnd_genWeightSpace_eq]; rw [map_add]
  map_smul χ hχ t x := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; 

Depends on / 依赖: Pi.smul_apply, finrank, map_add, map_lie, map_smul, smul_add, smul_apply, smul_comm, smul_right_inj, trace_comp_toEnd_genWeightSpace_eq, zero_lt_finrank_genWeightSpace
-/
instance instLinearWeightsOfCharZero [CharZero R] :
    LinearWeights R L M where
  map_add χ hχ x y := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; rw [smul_add]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply]; rw [← trace_comp_toEnd_genWeightSpace_eq]; rw [map_add]
  map_smul χ hχ t x := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; rw [smul_comm]; rw [← Pi.smul_apply]; rw [← Pi.smul_apply (finrank R _)]; rw [← trace_comp_toEnd_genWeightSpace_eq]; rw [map_smul]
  map_lie χ hχ x y := by
    rw [← smul_right_inj (zero_lt_finrank_genWeightSpace hχ).ne']; rw [nsmul_zero]; rw [← Pi.smul_apply]; rw [← trace_comp_toEnd_genWeightSpace_eq]; rw [LinearMap.comp_apply]; rw [LieHom.coe_toLinearMap]; rw [LieHom.map_lie]; rw [Ring.lie_def]; rw [map_sub]; rw [LinearMap.trace_mul_comm]; rw [sub_self]

end FiniteDimensional

variable [LieRing.IsNilpotent L] (χ : L -> R)

/--
Definition of `shiftedGenWeightSpace` / `shiftedGenWeightSpace` 的定义

English:
definition shiftedGenWeightSpace
  body: genWeightSpace M χ

中文:
定义 shiftedGenWeightSpace
  定义体: genWeightSpace M χ

Depends on / 依赖: genWeightSpace
-/
def shiftedGenWeightSpace := genWeightSpace M χ

namespace shiftedGenWeightSpace

/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: [h : Nontrivial (shiftedGenWeightSpace R L M χ)]
  statement: genWeightSpace M χ != ⊥
  proof: (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h

中文:
引理 aux
  条件: [h : 非平凡 (shiftedGenWeightSpace R L M χ)]
  结论: genWeightSpace M χ != ⊥
  证明: (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h
-/
private lemma aux [h : Nontrivial (shiftedGenWeightSpace R L M χ)] : genWeightSpace M χ != ⊥ :=
  (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h

variable [LinearWeights R L M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRingModule L (shiftedGenWeightSpace R L M χ)
  body: ⁅x, m⁆ - χ x • m
  add_lie x y m := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [add_lie, LinearWeights.map_add χ (aux R L M χ), add_smul]
    abel
  lie_add x m n := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [lie_add, smul_add]
    abel
  leibniz_lie x y 

中文:
实例 :
  签名: Lie环模 L (shiftedGenWeightSpace R L M χ)
  定义体: ⁅x, m⁆ - χ x • m
  add_lie x y m := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [add_lie, LinearWeights.map_add χ (aux R L M χ), add_smul]
    abel
  lie_add x m n := by
    nontriviality shiftedGenWeightSpace R L M χ
    simp only [lie_add, smul_add]
    abel
  leibniz_lie x y 
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

/--
lemma `coe_lie_shiftedGenWeightSpace_apply` / 引理 `coe_lie_shiftedGenWeightSpace_apply`

English:
lemma coe_lie_shiftedGenWeightSpace_apply
  given: (x : L) (m : shiftedGenWeightSpace R L M χ)
  proof: LieRingModule.toBracket
    ⁅x, m⁆ = ⁅x, (m : M)⁆ - χ x • m :=
  rfl

中文:
引理 coe_lie_shiftedGenWeightSpace_apply
  条件: (x : L) (m : shiftedGenWeightSpace R L M χ)
  证明: LieRingModule.toBracket
    ⁅x, m⁆ = ⁅x, (m : M)⁆ - χ x • m :=
  rfl
-/
@[simp] lemma coe_lie_shiftedGenWeightSpace_apply (x : L) (m : shiftedGenWeightSpace R L M χ) :
    letI : Bracket L (shiftedGenWeightSpace R L M χ) := LieRingModule.toBracket
    ⁅x, m⁆ = ⁅x, (m : M)⁆ - χ x • m :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule R L (shiftedGenWeightSpace R L M χ)
  body: by
    nontriviality shiftedGenWeightSpace R L M χ
    apply Subtype.ext
    rw [coe_lie_shiftedGenWeightSpace_apply]
    simp only [smul_lie, LinearWeights.map_smul χ (aux R L M χ), smul_assoc t, SetLike.val_smul]
    rw [← smul_sub]
    congr
  lie_smul t x m := by
    nontriviality shiftedGenWeig

中文:
实例 :
  签名: Lie模 R L (shiftedGenWeightSpace R L M χ)
  定义体: by
    nontriviality shiftedGenWeightSpace R L M χ
    apply Subtype.ext
    rw [coe_lie_shiftedGenWeightSpace_apply]
    simp only [smul_lie, LinearWeights.map_smul χ (aux R L M χ), smul_assoc t, SetLike.val_smul]
    rw [← smul_sub]
    congr
  lie_smul t x m := by
    nontriviality shiftedGenWeig

Depends on / 依赖: LinearWeights, LinearWeights.map_smul, SetLike, SetLike.val_smul, Subtype, Subtype.ext, coe_lie_shiftedGenWeightSpace_apply, lie_smul, map_smul, nontriviality, shiftedGenWeightSpace, smul_assoc, smul_comm, smul_lie, smul_sub, val_smul
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
    rw [smul_comm (χ x)]; rw [← smul_sub]
    congr

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: : genWeightSpace M χ ≃ₗ[R] shiftedGenWeightSpace R L M χ
  body: LinearEquiv.refl R _

中文:
定义 shift
  签名: : genWeightSpace M χ ≃ₗ[R] shiftedGenWeightSpace R L M χ
  定义体: LinearEquiv.refl R _
-/
@[simps!] def shift : genWeightSpace M χ ≃ₗ[R] shiftedGenWeightSpace R L M χ := LinearEquiv.refl R _

/--
lemma `toEnd_eq` / 引理 `toEnd_eq`

English:
lemma toEnd_eq
  given: (x : L)
  proof: by
  tauto

中文:
引理 toEnd_eq
  条件: (x : L)
  证明: by
  tauto
-/
lemma toEnd_eq (x : L) :
    toEnd R L (shiftedGenWeightSpace R L M χ) x =
    (shift R L M χ).conj (toEnd R L (genWeightSpace M χ) x - χ x • LinearMap.id) := by
  tauto

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherian
  signature: R M] : IsNilpotent L (shiftedGenWeightSpace R L M χ)
  body: LieModule.isNilpotent_iff_forall'.mpr fun x => isNilpotent_toEnd_sub_algebraMap M χ x

中文:
实例 [是Noether
  签名: R M] : 是幂零 L (shiftedGenWeightSpace R L M χ)
  定义体: LieModule.isNilpotent_iff_forall'.mpr fun x => isNilpotent_toEnd_sub_algebraMap M χ x

Depends on / 依赖: LieModule, LieModule.isNilpotent_iff_forall, isNilpotent_iff_forall, isNilpotent_toEnd_sub_algebraMap
-/
instance [IsNoetherian R M] : IsNilpotent L (shiftedGenWeightSpace R L M χ) :=
  LieModule.isNilpotent_iff_forall'.mpr fun x => isNilpotent_toEnd_sub_algebraMap M χ x

end shiftedGenWeightSpace

open shiftedGenWeightSpace in
/--
lemma `exists_forall_lie_eq_smul` / 引理 `exists_forall_lie_eq_smul`

English:
lemma exists_forall_lie_eq_smul
  given: [LinearWeights R L M] [IsNoetherian R M] (χ : Weight R L M)
  proof: by
  replace hχ : Nontrivial (shiftedGenWeightSpace R L M χ) :=
    (LieSubmodule.nontrivial_iff_ne_bot R L M).mpr χ.genWeightSpace_ne_bot
  obtain ⟨⟨⟨m, _⟩, hm₁⟩, hm₂⟩ :=
    @exists_ne _ (nontrivial_max_triv_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)) 0
  simp_rw [mem_maxTrivSubmodule, Sub

中文:
引理 存在_对任意_lie_eq_smul
  条件: [LinearWeights R L M] [是Noether R M] (χ : Weight R L M)
  证明: by
  replace hχ : Nontrivial (shiftedGenWeightSpace R L M χ) :=
    (LieSubmodule.nontrivial_iff_ne_bot R L M).mpr χ.genWeightSpace_ne_bot
  obtain ⟨⟨⟨m, _⟩, hm₁⟩, hm₂⟩ :=
    @exists_ne _ (nontrivial_max_triv_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)) 0
  simp_rw [mem_maxTrivSubmodule, Sub

Depends on / 依赖: LieSubmodule, LieSubmodule.mk_eq_zero, LieSubmodule.nontrivial_iff_ne_bot, Nontrivial, Subtype, Subtype.ext_iff, ZeroMemClass, ZeroMemClass.coe_zero, coe_lie_shiftedGenWeightSpace_apply, coe_zero, exists_ne, ext_iff, genWeightSpace_ne_bot, mem_maxTrivSubmodule, mk_eq_zero, nontrivial_iff_ne_bot, nontrivial_max_triv_of_isNilpotent, replace, shiftedGenWeightSpace, simp_rw
-/
lemma exists_forall_lie_eq_smul [LinearWeights R L M] [IsNoetherian R M] (χ : Weight R L M) :
    exists m : M, m != 0 ∧ forall x : L, ⁅x, m⁆ = χ x • m := by
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

/--
lemma `exists_nontrivial_weightSpace_of_isNilpotent` / 引理 `exists_nontrivial_weightSpace_of_isNilpotent`

English:
lemma exists_nontrivial_weightSpace_of_isNilpotent
  statement: [Field k] [LieAlgebra k L] [Module k M]
  proof: by
  obtain ⟨χ⟩ : Nonempty (Weight k L M) := by
    by_contra! contra
    simpa only [iSup_of_empty, bot_ne_top] using LieModule.iSup_genWeightSpace_eq_top' k L M
  obtain ⟨m, hm₀, hm⟩ := exists_forall_lie_eq_smul k L M χ
  simp only [LieSubmodule.nontrivial_iff_ne_bot, LieSubmodule.eq_bot_iff, ne_e

中文:
引理 存在_nontrivial_weightSpace_of_isNilpotent
  结论: [域 k] [Lie代数 k L] [模 k M]
  证明: by
  obtain ⟨χ⟩ : Nonempty (Weight k L M) := by
    by_contra! contra
    simpa only [iSup_of_empty, bot_ne_top] using LieModule.iSup_genWeightSpace_eq_top' k L M
  obtain ⟨m, hm₀, hm⟩ := exists_forall_lie_eq_smul k L M χ
  simp only [LieSubmodule.nontrivial_iff_ne_bot, LieSubmodule.eq_bot_iff, ne_e

Depends on / 依赖: LieModule, LieModule.iSup_genWeightSpace_eq_top, LieSubmodule, LieSubmodule.eq_bot_iff, LieSubmodule.nontrivial_iff_ne_bot, Nonempty, Weight, bot_ne_top, contra, eq_bot_iff, exists_forall_lie_eq_smul, iSup_genWeightSpace_eq_top, iSup_of_empty, mem_weightSpace, ne_eq, nontrivial_iff_ne_bot, not_forall, toLinear
-/
lemma exists_nontrivial_weightSpace_of_isNilpotent [Field k] [LieAlgebra k L] [Module k M]
    [Module.Finite k M] [LieModule k L M] [LinearWeights k L M]
    [IsTriangularizable k L M] [Nontrivial M] :
    exists χ : Module.Dual k L, Nontrivial (weightSpace M χ) := by
  obtain ⟨χ⟩ : Nonempty (Weight k L M) := by
    by_contra! contra
    simpa only [iSup_of_empty, bot_ne_top] using LieModule.iSup_genWeightSpace_eq_top' k L M
  obtain ⟨m, hm₀, hm⟩ := exists_forall_lie_eq_smul k L M χ
  simp only [LieSubmodule.nontrivial_iff_ne_bot, LieSubmodule.eq_bot_iff, ne_eq, not_forall]
  exact ⟨χ.toLinear, m, by simpa [mem_weightSpace], hm₀⟩

end LieModule
