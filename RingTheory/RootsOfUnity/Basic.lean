/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.RingTheory.IntegralDomain

-- TODO: remove Mathlib.Algebra.CharP.Reduced and move the last two lemmas to Lemmas

/-!
# Roots of unity

We define roots of unity in the context of an arbitrary commutative monoid,
as a subgroup of the group of units.

## Main definitions

* `rootsOfUnity n M`, for `n : ℕ` is the subgroup of the units of a commutative monoid `M`
  consisting of elements `x` that satisfy `x ^ n = 1`.

## Main results

* `rootsOfUnity.isCyclic`: the roots of unity in an integral domain form a cyclic group.

## Implementation details

It is desirable that `rootsOfUnity` is a subgroup,
and it will mainly be applied to rings (e.g. the ring of integers in a number field) and fields.
We therefore implement it as a subgroup of the units of a commutative monoid.

We have chosen to define `rootsOfUnity n` for `n : ℕ` and add a `[NeZero n]` typeclass
assumption when we need `n` to be non-zero (which is the case for most interesting statements).
Note that `rootsOfUnity 0 M` is the top subgroup of `Mˣ` (as the condition `ζ^0 = 1` is
satisfied for all units).
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

variable {M N G R S F : Type*}
variable [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

section rootsOfUnity

variable {k l : Nat}

/--
Definition of `rootsOfUnity` / `rootsOfUnity` 的定义

English:
definition rootsOfUnity
  signature: (k : Nat) (M : Type*) [CommMonoid M]
  body: {ζ | ζ ^ k = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_ofPred_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_ofPred_eq, inv_pow, inv_one]

@[simp]

中文:
定义 rootsOfUnity
  签名: (k : 自然数) (M : 类型) [交换幺半群 M]
  定义体: {ζ | ζ ^ k = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_ofPred_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_ofPred_eq, inv_pow, inv_one]

@[simp]
-/
def rootsOfUnity (k : Nat) (M : Type*) [CommMonoid M] : Subgroup Mˣ where
  carrier := {ζ | ζ ^ k = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_ofPred_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_ofPred_eq, inv_pow, inv_one]

@[simp]
/--
theorem `mem_rootsOfUnity` / 定理 `mem_rootsOfUnity`

English:
theorem mem_rootsOfUnity
  given: (k : Nat) (ζ : Mˣ)
  statement: ζ in rootsOfUnity k M ↔ ζ ^ k = 1
  proof: Iff.rfl

中文:
定理 mem_rootsOfUnity
  条件: (k : 自然数) (ζ : Mˣ)
  结论: ζ in rootsOfUnity k M ↔ ζ ^ k = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_rootsOfUnity (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnity k M ↔ ζ ^ k = 1 :=
  Iff.rfl

/--
theorem `rootsOfUnity_eq_ker` / 定理 `rootsOfUnity_eq_ker`

English:
theorem rootsOfUnity_eq_ker
  statement: rootsOfUnity k M = (powMonoidHom k).ker
  proof: by
  rfl

中文:
定理 rootsOfUnity_eq_ker
  结论: rootsOfUnity k M = (powMonoidHom k).ker
  证明: by
  rfl
-/
theorem rootsOfUnity_eq_ker : rootsOfUnity k M = (powMonoidHom k).ker := by
  rfl

/--
theorem `ker_zpowGroupHom_eq_rootsOfUnity` / 定理 `ker_zpowGroupHom_eq_rootsOfUnity`

English:
theorem ker_zpowGroupHom_eq_rootsOfUnity
  given: {k : Int}
  proof: by
  ext; simp

中文:
定理 ker_zpowGroupHom_eq_rootsOfUnity
  条件: {k : 整数}
  证明: by
  ext; simp
-/
theorem ker_zpowGroupHom_eq_rootsOfUnity {k : Int} :
    (zpowGroupHom k).ker = rootsOfUnity k.natAbs M := by
  ext; simp

/--
theorem `mem_rootsOfUnity'` / 定理 `mem_rootsOfUnity'`

English:
theorem mem_rootsOfUnity'
  given: (k : Nat) (ζ : Mˣ)
  statement: ζ in rootsOfUnity k M ↔ (ζ : M) ^ k = 1
  proof: by
  rw [mem_rootsOfUnity]; norm_cast

@[simp]

中文:
定理 mem_rootsOfUnity'
  条件: (k : 自然数) (ζ : Mˣ)
  结论: ζ in rootsOfUnity k M ↔ (ζ : M) ^ k = 1
  证明: by
  rw [mem_rootsOfUnity]; norm_cast

@[simp]

Depends on / 依赖: mem_rootsOfUnity
-/
theorem mem_rootsOfUnity' (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnity k M ↔ (ζ : M) ^ k = 1 := by
  rw [mem_rootsOfUnity]; norm_cast

@[simp]
/--
theorem `rootsOfUnity_one` / 定理 `rootsOfUnity_one`

English:
theorem rootsOfUnity_one
  given: (M : Type*) [CommMonoid M]
  statement: rootsOfUnity 1 M = ⊥
  proof: by
  ext1
  simp only [mem_rootsOfUnity, pow_one, Subgroup.mem_bot]

@[simp]

中文:
定理 rootsOfUnity_one
  条件: (M : 类型) [交换幺半群 M]
  结论: rootsOfUnity 1 M = ⊥
  证明: by
  ext1
  simp only [mem_rootsOfUnity, pow_one, Subgroup.mem_bot]

@[simp]

Depends on / 依赖: Subgroup, Subgroup.mem_bot, mem_bot, mem_rootsOfUnity, pow_one
-/
theorem rootsOfUnity_one (M : Type*) [CommMonoid M] : rootsOfUnity 1 M = ⊥ := by
  ext1
  simp only [mem_rootsOfUnity, pow_one, Subgroup.mem_bot]

@[simp]
/--
lemma `rootsOfUnity_zero` / 引理 `rootsOfUnity_zero`

English:
lemma rootsOfUnity_zero
  given: (M : Type*) [CommMonoid M]
  statement: rootsOfUnity 0 M = ⊤
  proof: by
  ext1
  simp only [mem_rootsOfUnity, pow_zero, Subgroup.mem_top]

中文:
引理 rootsOfUnity_zero
  条件: (M : 类型) [交换幺半群 M]
  结论: rootsOfUnity 0 M = ⊤
  证明: by
  ext1
  simp only [mem_rootsOfUnity, pow_zero, Subgroup.mem_top]

Depends on / 依赖: Subgroup, Subgroup.mem_top, mem_rootsOfUnity, mem_top, pow_zero
-/
lemma rootsOfUnity_zero (M : Type*) [CommMonoid M] : rootsOfUnity 0 M = ⊤ := by
  ext1
  simp only [mem_rootsOfUnity, pow_zero, Subgroup.mem_top]

/--
theorem `rootsOfUnity.coe_injective` / 定理 `rootsOfUnity.coe_injective`

English:
theorem rootsOfUnity.coe_injective
  given: {n : Nat}
  proof: Units.val_injective.comp Subtype.val_injective

中文:
定理 rootsOfUnity.coe_injective
  条件: {n : 自然数}
  证明: Units.val_injective.comp Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, Units.val_injective.comp, val_injective
-/
theorem rootsOfUnity.coe_injective {n : Nat} :
    Function.Injective (fun x : rootsOfUnity n M => x.val.val) :=
  Units.val_injective.comp Subtype.val_injective

/-- Make an element of `rootsOfUnity` from a member of the base ring, and a proof that it has
a positive power equal to one. -/
@[simps! coe_val]
/--
Definition of `rootsOfUnity.mkOfPowEq` / `rootsOfUnity.mkOfPowEq` 的定义

English:
definition rootsOfUnity.mkOfPowEq
  signature: (ζ : M) {n : Nat} [NeZero n] (h : ζ ^ n = 1)
  body: ⟨Units.ofPowEqOne ζ n h NeZero.ne n, Units.pow_ofPowEqOne _ _⟩

@[simp]

中文:
定义 rootsOfUnity.mkOfPowEq
  签名: (ζ : M) {n : 自然数} [NeZero n] (h : ζ ^ n = 1)
  定义体: ⟨Units.ofPowEqOne ζ n h NeZero.ne n, Units.pow_ofPowEqOne _ _⟩

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, Units.ofPowEqOne, Units.pow_ofPowEqOne, ofPowEqOne, pow_ofPowEqOne
-/
def rootsOfUnity.mkOfPowEq (ζ : M) {n : Nat} [NeZero n] (h : ζ ^ n = 1) : rootsOfUnity n M :=
⟨Units.ofPowEqOne ζ n h NeZero.ne n, Units.pow_ofPowEqOne _ _⟩

@[simp]
/--
theorem `rootsOfUnity.coe_mkOfPowEq` / 定理 `rootsOfUnity.coe_mkOfPowEq`

English:
theorem rootsOfUnity.coe_mkOfPowEq
  given: {ζ : M} {n : Nat} [NeZero n] (h : ζ ^ n = 1)
  proof: rfl

中文:
定理 rootsOfUnity.coe_mkOfPowEq
  条件: {ζ : M} {n : 自然数} [NeZero n] (h : ζ ^ n = 1)
  证明: rfl
-/
theorem rootsOfUnity.coe_mkOfPowEq {ζ : M} {n : Nat} [NeZero n] (h : ζ ^ n = 1) :
    ((rootsOfUnity.mkOfPowEq _ h : Mˣ) : M) = ζ :=
  rfl

/--
theorem `rootsOfUnity_le_of_dvd` / 定理 `rootsOfUnity_le_of_dvd`

English:
theorem rootsOfUnity_le_of_dvd
  given: (h : k ∣ l)
  statement: rootsOfUnity k M <= rootsOfUnity l M
  proof: by
  obtain ⟨d, rfl⟩ := h
  intro ζ h
  simp_all only [mem_rootsOfUnity, pow_mul, one_pow]

中文:
定理 rootsOfUnity_le_of_dvd
  条件: (h : k ∣ l)
  结论: rootsOfUnity k M <= rootsOfUnity l M
  证明: by
  obtain ⟨d, rfl⟩ := h
  intro ζ h
  simp_all only [mem_rootsOfUnity, pow_mul, one_pow]

Depends on / 依赖: mem_rootsOfUnity, one_pow, pow_mul
-/
theorem rootsOfUnity_le_of_dvd (h : k ∣ l) : rootsOfUnity k M <= rootsOfUnity l M := by
  obtain ⟨d, rfl⟩ := h
  intro ζ h
  simp_all only [mem_rootsOfUnity, pow_mul, one_pow]

/--
theorem `map_rootsOfUnity` / 定理 `map_rootsOfUnity`

English:
theorem map_rootsOfUnity
  given: (f : Mˣ ->* Nˣ) (k : Nat)
  statement: (rootsOfUnity k M).map f <= rootsOfUnity k N
  proof: by
  rintro _ ⟨ζ, h, rfl⟩
  simp_all only [← map_pow, mem_rootsOfUnity, SetLike.mem_coe, map_one]

中文:
定理 map_rootsOfUnity
  条件: (f : Mˣ ->* Nˣ) (k : 自然数)
  结论: (rootsOfUnity k M).map f <= rootsOfUnity k N
  证明: by
  rintro _ ⟨ζ, h, rfl⟩
  simp_all only [← map_pow, mem_rootsOfUnity, SetLike.mem_coe, map_one]

Depends on / 依赖: SetLike, SetLike.mem_coe, map_one, map_pow, mem_coe, mem_rootsOfUnity
-/
theorem map_rootsOfUnity (f : Mˣ ->* Nˣ) (k : Nat) : (rootsOfUnity k M).map f <= rootsOfUnity k N := by
  rintro _ ⟨ζ, h, rfl⟩
  simp_all only [← map_pow, mem_rootsOfUnity, SetLike.mem_coe, map_one]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (rootsOfUnity 1 M)
  body: by simp [subsingleton_iff]

中文:
实例 :
  签名: 子单例 (rootsOfUnity 1 M)
  定义体: by simp [subsingleton_iff]
-/
instance : Subsingleton (rootsOfUnity 1 M) := by simp [subsingleton_iff]

/--
lemma `rootsOfUnity_inf_rootsOfUnity` / 引理 `rootsOfUnity_inf_rootsOfUnity`

English:
lemma rootsOfUnity_inf_rootsOfUnity
  given: {m n : Nat}
  proof: by
  ext
  simp

中文:
引理 rootsOfUnity_inf_rootsOfUnity
  条件: {m n : 自然数}
  证明: by
  ext
  simp
-/
lemma rootsOfUnity_inf_rootsOfUnity {m n : Nat} :
    (rootsOfUnity m M ⊓ rootsOfUnity n M) = rootsOfUnity (m.gcd n) M := by
  ext
  simp

/--
lemma `disjoint_rootsOfUnity_of_coprime` / 引理 `disjoint_rootsOfUnity_of_coprime`

English:
lemma disjoint_rootsOfUnity_of_coprime
  given: {m n : Nat} (h : m.Coprime n)
  proof: by
  simp [disjoint_iff_inf_le, rootsOfUnity_inf_rootsOfUnity, Nat.coprime_iff_gcd_eq_one.mp h]

@[norm_cast]

中文:
引理 disjoint_rootsOfUnity_of_coprime
  条件: {m n : 自然数} (h : m.Coprime n)
  证明: by
  simp [disjoint_iff_inf_le, rootsOfUnity_inf_rootsOfUnity, Nat.coprime_iff_gcd_eq_one.mp h]

@[norm_cast]

Depends on / 依赖: Nat.coprime_iff_gcd_eq_one.mp, coprime_iff_gcd_eq_one, disjoint_iff_inf_le, rootsOfUnity_inf_rootsOfUnity
-/
lemma disjoint_rootsOfUnity_of_coprime {m n : Nat} (h : m.Coprime n) :
    Disjoint (rootsOfUnity m M) (rootsOfUnity n M) := by
  simp [disjoint_iff_inf_le, rootsOfUnity_inf_rootsOfUnity, Nat.coprime_iff_gcd_eq_one.mp h]

@[norm_cast]
/--
theorem `rootsOfUnity.coe_pow` / 定理 `rootsOfUnity.coe_pow`

English:
theorem rootsOfUnity.coe_pow
  given: [CommMonoid R] (ζ : rootsOfUnity k R) (m : Nat)
  proof: by
  rw [Subgroup.coe_pow]; rw [Units.val_pow_eq_pow_val]

中文:
定理 rootsOfUnity.coe_pow
  条件: [交换幺半群 R] (ζ : rootsOfUnity k R) (m : 自然数)
  证明: by
  rw [Subgroup.coe_pow]; rw [Units.val_pow_eq_pow_val]

Depends on / 依赖: Subgroup, Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_pow, val_pow_eq_pow_val
-/
theorem rootsOfUnity.coe_pow [CommMonoid R] (ζ : rootsOfUnity k R) (m : Nat) :
    (((ζ ^ m :) : Rˣ) : R) = ((ζ : Rˣ) : R) ^ m := by
  rw [Subgroup.coe_pow]; rw [Units.val_pow_eq_pow_val]

/--
Definition of `rootsOfUnityUnitsMulEquiv` / `rootsOfUnityUnitsMulEquiv` 的定义

English:
definition rootsOfUnityUnitsMulEquiv
  signature: (M : Type*) [CommMonoid M] (n : Nat)
  body: ⟨ζ.val, (mem_rootsOfUnity ..).mpr (mem_rootsOfUnity' ..).mp ζ.prop⟩
  invFun ζ := ⟨toUnits ζ.val, by
    simp only [mem_rootsOfUnity, ← map_pow, EmbeddingLike.map_eq_one_iff]
    exact (mem_rootsOfUnity ..).mp ζ.prop⟩
  left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
  right_inv ζ :=

中文:
定义 rootsOfUnityUnitsMulEquiv
  签名: (M : 类型) [交换幺半群 M] (n : 自然数)
  定义体: ⟨ζ.val, (mem_rootsOfUnity ..).mpr (mem_rootsOfUnity' ..).mp ζ.prop⟩
  invFun ζ := ⟨toUnits ζ.val, by
    simp only [mem_rootsOfUnity, ← map_pow, EmbeddingLike.map_eq_one_iff]
    exact (mem_rootsOfUnity ..).mp ζ.prop⟩
  left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
  right_inv ζ :=

Depends on / 依赖: mem_rootsOfUnity
-/
def rootsOfUnityUnitsMulEquiv (M : Type*) [CommMonoid M] (n : Nat) :
    rootsOfUnity n Mˣ ≃* rootsOfUnity n M where
toFun ζ := ⟨ζ.val, (mem_rootsOfUnity ..).mpr (mem_rootsOfUnity' ..).mp ζ.prop⟩
  invFun ζ := ⟨toUnits ζ.val, by
    simp only [mem_rootsOfUnity, ← map_pow, EmbeddingLike.map_eq_one_iff]
    exact (mem_rootsOfUnity ..).mp ζ.prop⟩
  left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
  right_inv ζ := by simp only [val_toUnits_apply, Subtype.coe_eta]
  map_mul' ζ ζ' := by simp only [Subgroup.coe_mul, Units.val_mul, MulMemClass.mk_mul_mk]

section CommMonoid

variable [CommMonoid R] [CommMonoid S] [FunLike F R S]

/--
Definition of `restrictRootsOfUnity` / `restrictRootsOfUnity` 的定义

English:
definition restrictRootsOfUnity
  signature: [MonoidHomClass F R S] (σ : F) (n : Nat)
  body: { toFun := fun ξ => ⟨Units.map σ (ξ : Rˣ), by
      rw [mem_rootsOfUnity]; rw [← map_pow]; rw [Units.ext_iff]; rw [Units.coe_map]; rw [ξ.prop]
      exact map_one σ⟩
    map_one' := by ext1; simp only [OneMemClass.coe_one, map_one]
    map_mul' := fun ξ₁ ξ₂ => by
      ext1; simp only [Subgroup.coe_

中文:
定义 restrictRootsOfUnity
  签名: [幺半群态射类 F R S] (σ : F) (n : 自然数)
  定义体: { toFun := fun ξ => ⟨Units.map σ (ξ : Rˣ), by
      rw [mem_rootsOfUnity]; rw [← map_pow]; rw [Units.ext_iff]; rw [Units.coe_map]; rw [ξ.prop]
      exact map_one σ⟩
    map_one' := by ext1; simp only [OneMemClass.coe_one, map_one]
    map_mul' := fun ξ₁ ξ₂ => by
      ext1; simp only [Subgroup.coe_

Depends on / 依赖: MulMemClass, MulMemClass.mk_mul_mk, OneMemClass, OneMemClass.coe_one, Subgroup, Subgroup.coe_mul, Units.coe_map, Units.ext_iff, Units.map, coe_map, coe_mul, coe_one, ext_iff, map_mul, map_one, map_pow, mem_rootsOfUnity, mk_mul_mk
-/
def restrictRootsOfUnity [MonoidHomClass F R S] (σ : F) (n : Nat) :
    rootsOfUnity n R ->* rootsOfUnity n S :=
  { toFun := fun ξ => ⟨Units.map σ (ξ : Rˣ), by
      rw [mem_rootsOfUnity]; rw [← map_pow]; rw [Units.ext_iff]; rw [Units.coe_map]; rw [ξ.prop]
      exact map_one σ⟩
    map_one' := by ext1; simp only [OneMemClass.coe_one, map_one]
    map_mul' := fun ξ₁ ξ₂ => by
      ext1; simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk] }

@[simp]
/--
theorem `restrictRootsOfUnity_coe_apply` / 定理 `restrictRootsOfUnity_coe_apply`

English:
theorem restrictRootsOfUnity_coe_apply
  given: [MonoidHomClass F R S] (σ : F) (ζ : rootsOfUnity k R)
  proof: rfl

中文:
定理 restrictRootsOfUnity_coe_apply
  条件: [幺半群态射类 F R S] (σ : F) (ζ : rootsOfUnity k R)
  证明: rfl
-/
theorem restrictRootsOfUnity_coe_apply [MonoidHomClass F R S] (σ : F) (ζ : rootsOfUnity k R) :
    (restrictRootsOfUnity σ k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

/-- Restrict a monoid isomorphism to the nth roots of unity. -/
nonrec def MulEquiv.restrictRootsOfUnity (σ : R ≃* S) (n : Nat) :
    rootsOfUnity n R ≃* rootsOfUnity n S where
  toFun := restrictRootsOfUnity σ n
  invFun := restrictRootsOfUnity σ.symm n
  left_inv ξ := by ext; exact σ.symm_apply_apply _
  right_inv ξ := by ext; exact σ.apply_symm_apply _
  map_mul' := (restrictRootsOfUnity _ n).map_mul

@[simp]
/--
theorem `MulEquiv.restrictRootsOfUnity_coe_apply` / 定理 `MulEquiv.restrictRootsOfUnity_coe_apply`

English:
theorem MulEquiv.restrictRootsOfUnity_coe_apply
  given: (σ : R ≃* S) (ζ : rootsOfUnity k R)
  proof: rfl

@[simp]

中文:
定理 乘法等价.restrictRootsOfUnity_coe_apply
  条件: (σ : R ≃* S) (ζ : rootsOfUnity k R)
  证明: rfl

@[simp]
-/
theorem MulEquiv.restrictRootsOfUnity_coe_apply (σ : R ≃* S) (ζ : rootsOfUnity k R) :
    (σ.restrictRootsOfUnity k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

@[simp]
/--
theorem `MulEquiv.restrictRootsOfUnity_symm` / 定理 `MulEquiv.restrictRootsOfUnity_symm`

English:
theorem MulEquiv.restrictRootsOfUnity_symm
  given: (σ : R ≃* S)
  proof: rfl

@[simp]

中文:
定理 乘法等价.restrictRootsOfUnity_symm
  条件: (σ : R ≃* S)
  证明: rfl

@[simp]
-/
theorem MulEquiv.restrictRootsOfUnity_symm (σ : R ≃* S) :
    (σ.restrictRootsOfUnity k).symm = σ.symm.restrictRootsOfUnity k :=
  rfl

@[simp]
/--
theorem `Units.val_set_image_rootsOfUnity` / 定理 `Units.val_set_image_rootsOfUnity`

English:
theorem Units.val_set_image_rootsOfUnity
  given: [NeZero k]
  proof: by
  ext x
  exact ⟨fun ⟨y,hy1,hy2⟩ => by rw [← hy2]; exact (mem_rootsOfUnity' k y).mp hy1,
    fun h => ⟨(rootsOfUnity.mkOfPowEq x h), ⟨Subtype.coe_prop (rootsOfUnity.mkOfPowEq x h), rfl⟩⟩⟩

中文:
定理 单位群.val_set_image_rootsOfUnity
  条件: [NeZero k]
  证明: by
  ext x
  exact ⟨fun ⟨y,hy1,hy2⟩ => by rw [← hy2]; exact (mem_rootsOfUnity' k y).mp hy1,
    fun h => ⟨(rootsOfUnity.mkOfPowEq x h), ⟨Subtype.coe_prop (rootsOfUnity.mkOfPowEq x h), rfl⟩⟩⟩

Depends on / 依赖: Subtype, Subtype.coe_prop, coe_prop, mem_rootsOfUnity, mkOfPowEq, rootsOfUnity, rootsOfUnity.mkOfPowEq
-/
theorem Units.val_set_image_rootsOfUnity [NeZero k] :
    ((↑) : Rˣ -> _) '' (rootsOfUnity k R) = {z : R | z^k = 1} := by
  ext x
  exact ⟨fun ⟨y,hy1,hy2⟩ => by rw [← hy2]; exact (mem_rootsOfUnity' k y).mp hy1,
    fun h => ⟨(rootsOfUnity.mkOfPowEq x h), ⟨Subtype.coe_prop (rootsOfUnity.mkOfPowEq x h), rfl⟩⟩⟩

/--
theorem `Units.val_set_image_rootsOfUnity_one` / 定理 `Units.val_set_image_rootsOfUnity_one`

English:
theorem Units.val_set_image_rootsOfUnity_one
  statement: ((↑) : Rˣ -> R) '' (rootsOfUnity 1 R) = {1}
  proof: by
  simp

中文:
定理 单位群.val_set_image_rootsOfUnity_one
  结论: ((↑) : Rˣ -> R) '' (rootsOfUnity 1 R) = {1}
  证明: by
  simp
-/
theorem Units.val_set_image_rootsOfUnity_one : ((↑) : Rˣ -> R) '' (rootsOfUnity 1 R) = {1} := by
  simp

end CommMonoid

section CommRing

variable [CommRing R]

open Set in
/--
theorem `Units.val_set_image_rootsOfUnity_two` / 定理 `Units.val_set_image_rootsOfUnity_two`

English:
theorem Units.val_set_image_rootsOfUnity_two
  given: [NoZeroDivisors R]
  proof: by
  ext x
  simp

中文:
定理 单位群.val_set_image_rootsOfUnity_two
  条件: [无零因子 R]
  证明: by
  ext x
  simp
-/
theorem Units.val_set_image_rootsOfUnity_two [NoZeroDivisors R] :
    ((↑) : Rˣ -> R) '' (rootsOfUnity 2 R) = {1, -1} := by
  ext x
  simp

/--
theorem `mem_rootsOfUnity_iff_isRoot` / 定理 `mem_rootsOfUnity_iff_isRoot`

English:
theorem mem_rootsOfUnity_iff_isRoot
  given: (k : Nat) (ζ : Rˣ)
  proof: by
  simp [-mem_rootsOfUnity, mem_rootsOfUnity', sub_eq_zero]

中文:
定理 mem_rootsOfUnity_iff_isRoot
  条件: (k : 自然数) (ζ : Rˣ)
  证明: by
  simp [-mem_rootsOfUnity, mem_rootsOfUnity', sub_eq_zero]

Depends on / 依赖: mem_rootsOfUnity, sub_eq_zero
-/
theorem mem_rootsOfUnity_iff_isRoot (k : Nat) (ζ : Rˣ) :
    ζ in rootsOfUnity k R ↔ (X ^ k - 1 : R[X]).IsRoot ζ := by
  simp [-mem_rootsOfUnity, mem_rootsOfUnity', sub_eq_zero]

end CommRing

section IsDomain

-- The following results need `k` to be nonzero.
variable [NeZero k] [CommRing R] [IsDomain R]

/--
theorem `mem_rootsOfUnity_iff_mem_nthRoots` / 定理 `mem_rootsOfUnity_iff_mem_nthRoots`

English:
theorem mem_rootsOfUnity_iff_mem_nthRoots
  given: {ζ : Rˣ}
  proof: by
  simp only [mem_rootsOfUnity, mem_nthRoots (NeZero.pos k), Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]

中文:
定理 mem_rootsOfUnity_iff_mem_nthRoots
  条件: {ζ : Rˣ}
  证明: by
  simp only [mem_rootsOfUnity, mem_nthRoots (NeZero.pos k), Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]

Depends on / 依赖: NeZero, NeZero.pos, Units.ext_iff, Units.val_one, Units.val_pow_eq_pow_val, ext_iff, mem_nthRoots, mem_rootsOfUnity, val_one, val_pow_eq_pow_val
-/
theorem mem_rootsOfUnity_iff_mem_nthRoots {ζ : Rˣ} :
    ζ in rootsOfUnity k R ↔ (ζ : R) in nthRoots k (1 : R) := by
  simp only [mem_rootsOfUnity, mem_nthRoots (NeZero.pos k), Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]

variable (k R)

/--
Definition of `rootsOfUnityEquivNthRoots` / `rootsOfUnityEquivNthRoots` 的定义

English:
definition rootsOfUnityEquivNthRoots
  signature: : rootsOfUnity k R ≃ { x // x in nthRoots k (1 : R) } where
  body: ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
  invFun x := by
    refine ⟨⟨x, ↑x ^ (k - 1 : Nat), ?_, ?_⟩, ?_⟩
    all_goals
      rcases x with ⟨x, hx⟩; rw [mem_nthRoots <| NeZero.pos k] at hx
      simp only [← pow_succ, ← pow_succ', hx, tsub_add_cancel_of_le NeZero.one_le]
    simp only [

中文:
定义 rootsOfUnityEquivNthRoots
  签名: : rootsOfUnity k R ≃ { x // x in nthRoots k (1 : R) } where
  定义体: ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
  invFun x := by
    refine ⟨⟨x, ↑x ^ (k - 1 : Nat), ?_, ?_⟩, ?_⟩
    all_goals
      rcases x with ⟨x, hx⟩; rw [mem_nthRoots <| NeZero.pos k] at hx
      simp only [← pow_succ, ← pow_succ', hx, tsub_add_cancel_of_le NeZero.one_le]
    simp only [

Depends on / 依赖: mem_rootsOfUnity_iff_mem_nthRoots, mem_rootsOfUnity_iff_mem_nthRoots.mp
-/
def rootsOfUnityEquivNthRoots : rootsOfUnity k R ≃ { x // x in nthRoots k (1 : R) } where
  toFun x := ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
  invFun x := by
    refine ⟨⟨x, ↑x ^ (k - 1 : Nat), ?_, ?_⟩, ?_⟩
    all_goals
      rcases x with ⟨x, hx⟩; rw [mem_nthRoots <| NeZero.pos k] at hx
      simp only [← pow_succ, ← pow_succ', hx, tsub_add_cancel_of_le NeZero.one_le]
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, hx, Units.val_one]

variable {k R}

@[simp]
/--
theorem `rootsOfUnityEquivNthRoots_apply` / 定理 `rootsOfUnityEquivNthRoots_apply`

English:
theorem rootsOfUnityEquivNthRoots_apply
  given: (x : rootsOfUnity k R)
  proof: rfl

@[simp]

中文:
定理 rootsOfUnityEquivNthRoots_apply
  条件: (x : rootsOfUnity k R)
  证明: rfl

@[simp]
-/
theorem rootsOfUnityEquivNthRoots_apply (x : rootsOfUnity k R) :
    (rootsOfUnityEquivNthRoots R k x : R) = ((x : Rˣ) : R) :=
  rfl

@[simp]
/--
theorem `rootsOfUnityEquivNthRoots_symm_apply` / 定理 `rootsOfUnityEquivNthRoots_symm_apply`

English:
theorem rootsOfUnityEquivNthRoots_symm_apply
  given: (x : { x // x in nthRoots k (1 : R) })
  proof: rfl

中文:
定理 rootsOfUnityEquivNthRoots_symm_apply
  条件: (x : { x // x in nthRoots k (1 : R) })
  证明: rfl
-/
theorem rootsOfUnityEquivNthRoots_symm_apply (x : { x // x in nthRoots k (1 : R) }) :
    (((rootsOfUnityEquivNthRoots R k).symm x : Rˣ) : R) = (x : R) :=
  rfl

variable (k R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (rootsOfUnity k R)
  body: by
  classical
  exact .of_equiv { x // x in nthRoots k (1 : R) } (rootsOfUnityEquivNthRoots R k).symm

中文:
实例 :
  签名: 有限 (rootsOfUnity k R)
  定义体: by
  classical
  exact .of_equiv { x // x in nthRoots k (1 : R) } (rootsOfUnityEquivNthRoots R k).symm
-/
instance : Finite (rootsOfUnity k R) := by
  classical
  exact .of_equiv { x // x in nthRoots k (1 : R) } (rootsOfUnityEquivNthRoots R k).symm

/--
Instance `rootsOfUnity.isCyclic` / 实例 `rootsOfUnity.isCyclic`

English:
instance rootsOfUnity.isCyclic
  signature: : IsCyclic (rootsOfUnity k R)
  body: isCyclic_of_injective_ringHom ((Units.coeHom R).comp (rootsOfUnity k R).subtype) coe_injective

中文:
实例 rootsOfUnity.isCyclic
  签名: : 是循环 (rootsOfUnity k R)
  定义体: isCyclic_of_injective_ringHom ((Units.coeHom R).comp (rootsOfUnity k R).subtype) coe_injective

Depends on / 依赖: Units.coeHom, coeHom, coe_injective, isCyclic_of_injective_ringHom, rootsOfUnity, subtype
-/
instance rootsOfUnity.isCyclic : IsCyclic (rootsOfUnity k R) :=
  isCyclic_of_injective_ringHom ((Units.coeHom R).comp (rootsOfUnity k R).subtype) coe_injective

/--
theorem `card_rootsOfUnity` / 定理 `card_rootsOfUnity`

English:
theorem card_rootsOfUnity
  statement: Nat.card (rootsOfUnity k R) <= k
  proof: by
  classical
  calc
    Nat.card (rootsOfUnity k R) = Nat.card { x // x in nthRoots k (1 : R) } :=
      Nat.card_congr (rootsOfUnityEquivNthRoots R k)
    _ = Fintype.card { x // x in nthRoots k (1 : R) } := Nat.card_eq_fintype_card
    _ <= Multiset.card (nthRoots k (1 : R)).attach := Multiset.c

中文:
定理 card_rootsOfUnity
  结论: 自然数.card (rootsOfUnity k R) <= k
  证明: by
  classical
  calc
    Nat.card (rootsOfUnity k R) = Nat.card { x // x in nthRoots k (1 : R) } :=
      Nat.card_congr (rootsOfUnityEquivNthRoots R k)
    _ = Fintype.card { x // x in nthRoots k (1 : R) } := Nat.card_eq_fintype_card
    _ <= Multiset.card (nthRoots k (1 : R)).attach := Multiset.c

Depends on / 依赖: Fintype, Fintype.card, Multiset, Multiset.card, Multiset.card_attach, Multiset.card_le_card, Multiset.dedup_le, Nat.card, Nat.card_congr, Nat.card_eq_fintype_card, attach, card_attach, card_congr, card_eq_fintype_card, card_le_card, card_nthRoots, classical, dedup_le, nthRoots, rootsOfUnity
-/
theorem card_rootsOfUnity : Nat.card (rootsOfUnity k R) <= k := by
  classical
  calc
    Nat.card (rootsOfUnity k R) = Nat.card { x // x in nthRoots k (1 : R) } :=
      Nat.card_congr (rootsOfUnityEquivNthRoots R k)
    _ = Fintype.card { x // x in nthRoots k (1 : R) } := Nat.card_eq_fintype_card
    _ <= Multiset.card (nthRoots k (1 : R)).attach := Multiset.card_le_card (Multiset.dedup_le _)
    _ = Multiset.card (nthRoots k (1 : R)) := Multiset.card_attach
    _ <= k := card_nthRoots k 1

variable {k R}

/--
theorem `map_rootsOfUnity_eq_pow_self` / 定理 `map_rootsOfUnity_eq_pow_self`

English:
theorem map_rootsOfUnity_eq_pow_self
  statement: [FunLike F R R] [MonoidHomClass F R R] (σ : F)
  proof: by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ k)
  rw [← restrictRootsOfUnity_coe_apply]; rw [hm]; rw [← zpow_mod_orderOf]; rw [← Int.toNat_of_nonneg
      (m.emod_nonneg (Int.natCast_ne_zero.mpr (pos_iff_ne_zero.mp (orderOf_pos ζ))))]; rw [zpow_natCast]; rw [rootsOfUnity.coe_p

中文:
定理 map_rootsOfUnity_eq_pow_self
  结论: [函数状 F R R] [幺半群态射类 F R R] (σ : F)
  证明: by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ k)
  rw [← restrictRootsOfUnity_coe_apply]; rw [hm]; rw [← zpow_mod_orderOf]; rw [← Int.toNat_of_nonneg
      (m.emod_nonneg (Int.natCast_ne_zero.mpr (pos_iff_ne_zero.mp (orderOf_pos ζ))))]; rw [zpow_natCast]; rw [rootsOfUnity.coe_p

Depends on / 依赖: Int.natCast_ne_zero.mpr, Int.toNat_of_nonneg, MonoidHom, MonoidHom.map_cyclic, coe_pow, emod_nonneg, m.emod_nonneg, map_cyclic, natCast_ne_zero, orderOf, orderOf_pos, pos_iff_ne_zero, pos_iff_ne_zero.mp, restrictRootsOfUnity, restrictRootsOfUnity_coe_apply, rootsOfUnity, rootsOfUnity.coe_pow, toNat_of_nonneg, zpow_mod_orderOf, zpow_natCast
-/
theorem map_rootsOfUnity_eq_pow_self [FunLike F R R] [MonoidHomClass F R R] (σ : F)
    (ζ : rootsOfUnity k R) :
    exists m : Nat, σ (ζ : Rˣ) = ((ζ : Rˣ) : R) ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ k)
  rw [← restrictRootsOfUnity_coe_apply]; rw [hm]; rw [← zpow_mod_orderOf]; rw [← Int.toNat_of_nonneg
      (m.emod_nonneg (Int.natCast_ne_zero.mpr (pos_iff_ne_zero.mp (orderOf_pos ζ))))]; rw [zpow_natCast]; rw [rootsOfUnity.coe_pow]
  exact ⟨(m % orderOf ζ).toNat, rfl⟩

instance {L : Type*} [LeftCancelMonoid L] [Finite L] :
    Finite (L ->* Rˣ) := by
  let S := rootsOfUnity (Monoid.exponent L) R
  have : Finite (L ->* S) := .of_injective _ DFunLike.coe_injective
  refine .of_surjective (fun f : L ->* S => (Subgroup.subtype _).comp f) fun f => ?_
  have H a : f a in S := by
    rw [mem_rootsOfUnity]; rw [← map_pow]; rw [Monoid.pow_exponent_eq_one]; rw [map_one]
  exact ⟨.codRestrict f S H, MonoidHom.ext fun _ => by simp⟩

end IsDomain

section Reduced

variable (R) [CommRing R] [IsReduced R]

-- simp normal form is `mem_rootsOfUnity_prime_pow_mul_iff'`
/--
theorem `mem_rootsOfUnity_prime_pow_mul_iff` / 定理 `mem_rootsOfUnity_prime_pow_mul_iff`

English:
theorem mem_rootsOfUnity_prime_pow_mul_iff
  given: (p k : Nat) (m : Nat) [ExpChar R p] {ζ : Rˣ}
  proof: by
  simp only [mem_rootsOfUnity', ExpChar.pow_prime_pow_mul_eq_one_iff]

中文:
定理 mem_rootsOfUnity_prime_pow_mul_iff
  条件: (p k : 自然数) (m : 自然数) [ExpChar R p] {ζ : Rˣ}
  证明: by
  simp only [mem_rootsOfUnity', ExpChar.pow_prime_pow_mul_eq_one_iff]

Depends on / 依赖: ExpChar, ExpChar.pow_prime_pow_mul_eq_one_iff, mem_rootsOfUnity, pow_prime_pow_mul_eq_one_iff
-/
theorem mem_rootsOfUnity_prime_pow_mul_iff (p k : Nat) (m : Nat) [ExpChar R p] {ζ : Rˣ} :
    ζ in rootsOfUnity (p ^ k * m) R ↔ ζ in rootsOfUnity m R := by
  simp only [mem_rootsOfUnity', ExpChar.pow_prime_pow_mul_eq_one_iff]

/-- A variant of `mem_rootsOfUnity_prime_pow_mul_iff` in terms of `ζ ^ _` -/
@[simp]
/--
theorem `mem_rootsOfUnity_prime_pow_mul_iff'` / 定理 `mem_rootsOfUnity_prime_pow_mul_iff'`

English:
theorem mem_rootsOfUnity_prime_pow_mul_iff'
  given: (p k : Nat) (m : Nat) [ExpChar R p] {ζ : Rˣ}
  proof: by
  rw [← mem_rootsOfUnity]; rw [mem_rootsOfUnity_prime_pow_mul_iff]

中文:
定理 mem_rootsOfUnity_prime_pow_mul_iff'
  条件: (p k : 自然数) (m : 自然数) [ExpChar R p] {ζ : Rˣ}
  证明: by
  rw [← mem_rootsOfUnity]; rw [mem_rootsOfUnity_prime_pow_mul_iff]

Depends on / 依赖: mem_rootsOfUnity, mem_rootsOfUnity_prime_pow_mul_iff
-/
theorem mem_rootsOfUnity_prime_pow_mul_iff' (p k : Nat) (m : Nat) [ExpChar R p] {ζ : Rˣ} :
    ζ ^ (p ^ k * m) = 1 ↔ ζ in rootsOfUnity m R := by
  rw [← mem_rootsOfUnity]; rw [mem_rootsOfUnity_prime_pow_mul_iff]

end Reduced

end rootsOfUnity

section cyclic

namespace IsCyclic

/-- The isomorphism from the group of group homomorphisms from a finite cyclic group `G` of order
`n` into another group `G'` to the group of `n`th roots of unity in `G'` determined by a generator
`g` of `G`. It sends `φ : G →* G'` to `φ g`. -/
noncomputable
/--
Definition of `monoidHomMulEquivRootsOfUnityOfGenerator` / `monoidHomMulEquivRootsOfUnityOfGenerator` 的定义

English:
definition monoidHomMulEquivRootsOfUnityOfGenerator
  signature: {G : Type*} [CommGroup G] {g : G}
  body: ⟨(IsUnit.map φ <| Group.isUnit g).unit, by
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      ← map_pow, pow_card_eq_one', map_one, Units.val_one]⟩
invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) by
    simpa only [orderOf_eq_card_of_for

中文:
定义 monoidHomMulEquivRootsOfUnityOfGenerator
  签名: {G : 类型} [交换群 G] {g : G}
  定义体: ⟨(IsUnit.map φ <| Group.isUnit g).unit, by
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      ← map_pow, pow_card_eq_one', map_one, Units.val_one]⟩
invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) by
    simpa only [orderOf_eq_card_of_for

Depends on / 依赖: Group.isUnit, IsUnit, IsUnit.map, IsUnit.unit_spec, MonoidHom, MonoidHom.eq_iff_eq_on_generator, Units.ext_iff, Units.val_eq_one, Units.val_one, Units.val_pow_eq_pow_val, eq_iff_eq_on_generator, ext_iff, invFun, isUnit, left_inv, map_one, map_pow, mem_rootsOfUnity, monoidHomOfFor, monoidHomOfForallMemZpowers
-/
def monoidHomMulEquivRootsOfUnityOfGenerator {G : Type*} [CommGroup G] {g : G}
    (hg : forall (x : G), x in Subgroup.zpowers g) (G' : Type*) [CommGroup G'] :
    (G ->* G') ≃* rootsOfUnity (Nat.card G) G' where
  toFun φ := ⟨(IsUnit.map φ <| Group.isUnit g).unit, by
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      ← map_pow, pow_card_eq_one', map_one, Units.val_one]⟩
invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) by
    simpa only [orderOf_eq_card_of_forall_mem_zpowers hg, orderOf_dvd_iff_pow_eq_one,
      ← Units.val_pow_eq_pow_val, Units.val_eq_one] using! ζ.prop
left_inv φ := (MonoidHom.eq_iff_eq_on_generator hg _ φ).mpr by
    simp only [IsUnit.unit_spec, monoidHomOfForallMemZpowers_apply_gen]
right_inv φ := Subtype.ext by
    simp only [monoidHomOfForallMemZpowers_apply_gen, IsUnit.unit_of_val_units]
  map_mul' x y := by
    simp only [MonoidHom.mul_apply, MulMemClass.mk_mul_mk, Subtype.mk.injEq, Units.ext_iff,
      IsUnit.unit_spec, Units.val_mul]

/--
lemma `monoidHom_mulEquiv_rootsOfUnity` / 引理 `monoidHom_mulEquiv_rootsOfUnity`

English:
lemma monoidHom_mulEquiv_rootsOfUnity
  statement: (G : Type*) [CommGroup G] [IsCyclic G]
  proof: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact ⟨monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

中文:
引理 monoidHom_mulEquiv_rootsOfUnity
  结论: (G : 类型) [交换群 G] [是循环 G]
  证明: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact ⟨monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, exists_generator, monoidHomMulEquivRootsOfUnityOfGenerator
-/
lemma monoidHom_mulEquiv_rootsOfUnity (G : Type*) [CommGroup G] [IsCyclic G]
    (G' : Type*) [CommGroup G'] :
Nonempty (G ->* G') ≃* rootsOfUnity (Nat.card G) G' := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact ⟨monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

end IsCyclic

end cyclic
