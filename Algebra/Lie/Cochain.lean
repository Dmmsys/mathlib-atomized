/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# Lie algebra cohomology in low degree

This file defines low degree cochains of Lie algebras with coefficients given by a module. They are
useful in the construction of central extensions, so we treat these easier cases separately from the
general theory of Lie algebra cohomology.

## Main definitions
* `LieAlgebra.oneCochain`: an abbreviation for a linear map.
* `LieAlgebra.twoCochain`: a submodule of bilinear maps, giving 2-cochains.
* `LieAlgebra.d₁₂`: The coboundary map taking 1-cochains to 2-cochains.
* `LieAlgebra.d₂₃`: A coboundary map taking 2-cochains to a space containing 3-cochains.
* `LieAlgebra.twoCocycle`: The submodule of 2-cocycles.

## TODO
* coboundaries, cohomology
* comparison to the Chevalley-Eilenberg complex.
* construction and classification of central extensions

## References
* [H. Cartan, S. Eilenberg, *Homological Algebra*](cartan-eilenberg-1956)

-/

@[expose] public section

namespace LieModule.Cohomology

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M]

/--
Definition of `oneCochain` / `oneCochain` 的定义

English:
abbreviation oneCochain
  body: L ->ₗ[R] M

中文:
缩写 oneCochain
  定义体: L ->ₗ[R] M
-/
abbrev oneCochain := L ->ₗ[R] M

/--
Definition of `twoCochain` / `twoCochain` 的定义

English:
definition twoCochain
  signature: : Submodule R (L ->ₗ[R] L ->ₗ[R] M) where
  body: {c | forall x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

中文:
定义 twoCochain
  签名: : 子模 R (L ->ₗ[R] L ->ₗ[R] M) where
  定义体: {c | forall x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]
-/
def twoCochain : Submodule R (L ->ₗ[R] L ->ₗ[R] M) where
  carrier := {c | forall x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

section

variable {R L M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (twoCochain R L M) L (L ->ₗ[R] M)
  body: fun a x => a.1 x
  coe_injective _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

中文:
实例 :
  签名: 函数状 (twoCochain R L M) L (L ->ₗ[R] M)
  定义体: fun a x => a.1 x
  coe_injective _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _
-/
instance : FunLike (twoCochain R L M) L (L ->ₗ[R] M) where
  coe := fun a x => a.1 x
  coe_injective _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (twoCochain R L M) R L (L ->ₗ[R] M)
  body: a.1.map_add
  map_smulₛₗ a := a.1.map_smul

@[simp]

中文:
实例 :
  签名: 线性映射类 (twoCochain R L M) R L (L ->ₗ[R] M)
  定义体: a.1.map_add
  map_smulₛₗ a := a.1.map_smul

@[simp]

Depends on / 依赖: map_add
-/
instance : LinearMapClass (twoCochain R L M) R L (L ->ₗ[R] M) where
  map_add a := a.1.map_add
  map_smulₛₗ a := a.1.map_smul

@[simp]
/--
lemma `mem_twoCochain_iff` / 引理 `mem_twoCochain_iff`

English:
lemma mem_twoCochain_iff
  given: {c : L ->ₗ[R] L ->ₗ[R] M}
  statement: c in twoCochain R L M ↔ forall x, c x x = 0
  proof: Iff.rfl

@[simp]

中文:
引理 mem_twoCochain_iff
  条件: {c : L ->ₗ[R] L ->ₗ[R] M}
  结论: c in twoCochain R L M ↔ 对任意 x, c x x = 0
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_twoCochain_iff {c : L ->ₗ[R] L ->ₗ[R] M} : c in twoCochain R L M ↔ forall x, c x x = 0 := Iff.rfl

@[simp]
/--
lemma `twoCochain_alt` / 引理 `twoCochain_alt`

English:
lemma twoCochain_alt
  given: (a : twoCochain R L M) (x : L)
  proof: a.2 x

中文:
引理 twoCochain_alt
  条件: (a : twoCochain R L M) (x : L)
  证明: a.2 x
-/
lemma twoCochain_alt (a : twoCochain R L M) (x : L) :
    a x x = 0 :=
  a.2 x

/--
lemma `twoCochain_skew` / 引理 `twoCochain_skew`

English:
lemma twoCochain_skew
  given: (a : twoCochain R L M) (x y : L)
  statement: - a x y = a y x
  proof: by
  rw [neg_eq_iff_add_eq_zero]; rw [add_comm]
  simpa [map_add, twoCochain_alt a x, twoCochain_alt a y] using twoCochain_alt a (x + y)

@[simp]

中文:
引理 twoCochain_skew
  条件: (a : twoCochain R L M) (x y : L)
  结论: - a x y = a y x
  证明: by
  rw [neg_eq_iff_add_eq_zero]; rw [add_comm]
  simpa [map_add, twoCochain_alt a x, twoCochain_alt a y] using twoCochain_alt a (x + y)

@[simp]

Depends on / 依赖: add_comm, map_add, neg_eq_iff_add_eq_zero, twoCochain_alt
-/
lemma twoCochain_skew (a : twoCochain R L M) (x y : L) : - a x y = a y x := by
  rw [neg_eq_iff_add_eq_zero]; rw [add_comm]
  simpa [map_add, twoCochain_alt a x, twoCochain_alt a y] using twoCochain_alt a (x + y)

@[simp]
/--
lemma `twoCochain_val_apply` / 引理 `twoCochain_val_apply`

English:
lemma twoCochain_val_apply
  given: (a : twoCochain R L M) (x : L)
  proof: rfl

@[simp]

中文:
引理 twoCochain_val_apply
  条件: (a : twoCochain R L M) (x : L)
  证明: rfl

@[simp]
-/
lemma twoCochain_val_apply (a : twoCochain R L M) (x : L) :
    a.val x = a x :=
  rfl

@[simp]
/--
lemma `add_apply_apply` / 引理 `add_apply_apply`

English:
lemma add_apply_apply
  given: (a b : twoCochain R L M) (x y : L)
  proof: by
  rfl


@[simp]

中文:
引理 add_apply_apply
  条件: (a b : twoCochain R L M) (x y : L)
  证明: by
  rfl


@[simp]
-/
lemma add_apply_apply (a b : twoCochain R L M) (x y : L) :
    (a + b) x y = a x y + b x y := by
  rfl


@[simp]
/--
lemma `smul_apply_apply` / 引理 `smul_apply_apply`

English:
lemma smul_apply_apply
  given: (r : R) (a : twoCochain R L M) (x y : L)
  proof: by
  rfl

中文:
引理 smul_apply_apply
  条件: (r : R) (a : twoCochain R L M) (x y : L)
  证明: by
  rfl
-/
lemma smul_apply_apply (r : R) (a : twoCochain R L M) (x y : L) :
    (r • a) x y = r • (a x y) := by
  rfl

end

variable [LieRingModule L M] [LieModule R L M]

/-- The coboundary operator taking degree 1 cochains to degree 2 cochains. -/
@[simps]
/--
Definition of `d₁₂` / `d₁₂` 的定义

English:
definition d₁₂
  signature: : oneCochain R L M ->ₗ[R] twoCochain R L M where
  body: { val :=
      { toFun x :=
          { toFun y := ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆
            map_add' _ _ := by simp; abel
            map_smul' _ _ := by simp [smul_sub] }
        map_add' _ _ := by ext; simp; abel
        map_smul' _ _ := by ext; simp [smul_sub] }
      property x := by simp }
  

中文:
定义 d₁₂
  签名: : oneCochain R L M ->ₗ[R] twoCochain R L M where
  定义体: { val :=
      { toFun x :=
          { toFun y := ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆
            map_add' _ _ := by simp; abel
            map_smul' _ _ := by simp [smul_sub] }
        map_add' _ _ := by ext; simp; abel
        map_smul' _ _ := by ext; simp [smul_sub] }
      property x := by simp }
  

Depends on / 依赖: map_add, map_smul, property, smul_sub
-/
def d₁₂ : oneCochain R L M ->ₗ[R] twoCochain R L M where
  toFun f :=
    { val :=
      { toFun x :=
          { toFun y := ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆
            map_add' _ _ := by simp; abel
            map_smul' _ _ := by simp [smul_sub] }
        map_add' _ _ := by ext; simp; abel
        map_smul' _ _ := by ext; simp [smul_sub] }
      property x := by simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

@[simp]
/--
lemma `d₁₂_apply_apply` / 引理 `d₁₂_apply_apply`

English:
lemma d₁₂_apply_apply
  given: (f : oneCochain R L M) (x y : L)
  proof: rfl

中文:
引理 d₁₂_apply_apply
  条件: (f : oneCochain R L M) (x y : L)
  证明: rfl
-/
lemma d₁₂_apply_apply (f : oneCochain R L M) (x y : L) :
    d₁₂ R L M f x y = ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆ := rfl

/--
lemma `d₁₂_apply_apply_ofTrivial` / 引理 `d₁₂_apply_apply_ofTrivial`

English:
lemma d₁₂_apply_apply_ofTrivial
  given: [LieModule.IsTrivial L M] (f : oneCochain R L M) (x y : L)
  proof: by
  simp [trivial_lie_zero]

中文:
引理 d₁₂_apply_apply_ofTrivial
  条件: [Lie模.是平凡 L M] (f : oneCochain R L M) (x y : L)
  证明: by
  simp [trivial_lie_zero]

Depends on / 依赖: trivial_lie_zero
-/
lemma d₁₂_apply_apply_ofTrivial [LieModule.IsTrivial L M] (f : oneCochain R L M) (x y : L) :
    d₁₂ R L M f x y = - f ⁅x, y⁆ := by
  simp [trivial_lie_zero]

/--
Definition of `d₂₃` / `d₂₃` 的定义

English:
definition d₂₃
  signature: : twoCochain R L M ->ₗ[R] L ->ₗ[R] L ->ₗ[R] L ->ₗ[R] M where
  body: {
    toFun x := {
      toFun y := {
        toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
        map_add' _ _ := by simp; abel
        map_smul' _ _ := by simp; abel_nf; simp }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; simp; a

中文:
定义 d₂₃
  签名: : twoCochain R L M ->ₗ[R] L ->ₗ[R] L ->ₗ[R] L ->ₗ[R] M where
  定义体: {
    toFun x := {
      toFun y := {
        toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
        map_add' _ _ := by simp; abel
        map_smul' _ _ := by simp; abel_nf; simp }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; simp; a
-/
def d₂₃ : twoCochain R L M ->ₗ[R] L ->ₗ[R] L ->ₗ[R] L ->ₗ[R] M where
  toFun a := {
    toFun x := {
      toFun y := {
        toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
        map_add' _ _ := by simp; abel
        map_smul' _ _ := by simp; abel_nf; simp }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; simp; abel_nf; simp }
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; simp; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp; abel_nf; simp

@[simp]
/--
lemma `d₂₃_apply` / 引理 `d₂₃_apply`

English:
lemma d₂₃_apply
  given: (a : twoCochain R L M) (x y z : L)
  proof: rfl

中文:
引理 d₂₃_apply
  条件: (a : twoCochain R L M) (x y z : L)
  证明: rfl
-/
lemma d₂₃_apply (a : twoCochain R L M) (x y z : L) :
    d₂₃ R L M a x y z =
      ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x :=
  rfl

/--
lemma `d₂₃_comp_d₁₂` / 引理 `d₂₃_comp_d₁₂`

English:
lemma d₂₃_comp_d₁₂
  statement: (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0
  proof: by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : d₁₂ R L M a x = (d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, d₂₃_apply, LinearMap.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x]; rw [leibniz_lie z x]; rw [leibniz_lie z y]
  ha

中文:
引理 d₂₃_comp_d₁₂
  结论: (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0
  证明: by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : d₁₂ R L M a x = (d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, d₂₃_apply, LinearMap.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x]; rw [leibniz_lie z x]; rw [leibniz_lie z y]
  ha

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.zero_apply, comp_apply, congr_arg, leibniz_lie, lie_lie, lie_neg, lie_ske, lie_skew, lie_sub, map_add, map_sub, oneCochain, sub_add_cancel, zero_apply
-/
lemma d₂₃_comp_d₁₂ : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : d₁₂ R L M a x = (d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, d₂₃_apply, LinearMap.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x]; rw [leibniz_lie z x]; rw [leibniz_lie z y]
  have : a ⁅y, ⁅z, x⁆⁆ = a ⁅x, ⁅z, y⁆⁆ + a ⁅z, ⁅y, x⁆⁆ := by
    rw [congr_arg a (leibniz_lie y z x)]; rw [← lie_skew]; rw [← lie_skew z y]; rw [lie_neg]; rw [map_add]
  simp only [lie_lie, sub_add_cancel, map_sub, ← lie_skew x y, ← lie_skew x z, ← lie_skew y z,
    lie_neg, map_neg, this]
  abel

/--
Definition of `twoCocycle` / `twoCocycle` 的定义

English:
definition twoCocycle
  signature: : Submodule R (twoCochain R L M)
  body: LinearMap.ker (d₂₃ R L M)

中文:
定义 twoCocycle
  签名: : 子模 R (twoCochain R L M)
  定义体: LinearMap.ker (d₂₃ R L M)

Depends on / 依赖: LinearMap, LinearMap.ker
-/
def twoCocycle : Submodule R (twoCochain R L M) := LinearMap.ker (d₂₃ R L M)

/--
lemma `mem_twoCocycle_iff` / 引理 `mem_twoCocycle_iff`

English:
lemma mem_twoCocycle_iff
  given: (a : twoCochain R L M)
  statement: a in twoCocycle R L M ↔ d₂₃ R L M a = 0
  proof: by
  simp [twoCocycle]

中文:
引理 mem_twoCocycle_iff
  条件: (a : twoCochain R L M)
  结论: a in twoCocycle R L M ↔ d₂₃ R L M a = 0
  证明: by
  simp [twoCocycle]

Depends on / 依赖: twoCocycle
-/
lemma mem_twoCocycle_iff (a : twoCochain R L M) : a in twoCocycle R L M ↔ d₂₃ R L M a = 0 := by
  simp [twoCocycle]

/--
lemma `mem_twoCocycle_iff_of_trivial` / 引理 `mem_twoCocycle_iff_of_trivial`

English:
lemma mem_twoCocycle_iff_of_trivial
  given: [LieModule.IsTrivial L M] (a : twoCochain R L M)
  proof: by
  constructor
  · intro h x y z
    rw [mem_twoCocycle_iff] at h
    have : (d₂₃ R L M) a x y z = 0 := (congrArg (fun b => b x y z = 0) h).mpr rfl
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub] at this
    rw [sub_eq_zero] at this
    rw [← twoCochain_skew a _ x]; rw [←

中文:
引理 mem_twoCocycle_iff_of_trivial
  条件: [Lie模.是平凡 L M] (a : twoCochain R L M)
  证明: by
  constructor
  · intro h x y z
    rw [mem_twoCocycle_iff] at h
    have : (d₂₃ R L M) a x y z = 0 := (congrArg (fun b => b x y z = 0) h).mpr rfl
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub] at this
    rw [sub_eq_zero] at this
    rw [← twoCochain_skew a _ x]; rw [←

Depends on / 依赖: LinearMap, LinearMap.zero_apply, add_zero, mem_twoCocycle_iff, sub_eq_zero, sub_self, trivial_lie_zero, twoCochain_skew, zero_apply, zero_sub
-/
lemma mem_twoCocycle_iff_of_trivial [LieModule.IsTrivial L M] (a : twoCochain R L M) :
    a in twoCocycle R L M ↔
      forall (x y z : L), a x ⁅y, z⁆ = a ⁅x, y⁆ z + a y ⁅x, z⁆ := by
  constructor
  · intro h x y z
    rw [mem_twoCocycle_iff] at h
    have : (d₂₃ R L M) a x y z = 0 := (congrArg (fun b => b x y z = 0) h).mpr rfl
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub] at this
    rw [sub_eq_zero] at this
    rw [← twoCochain_skew a _ x]; rw [← twoCochain_skew a _ y]; rw [← this]
    abel
  · intro h
    ext x y z
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub, LinearMap.zero_apply]
    rw [← twoCochain_skew a x]; rw [← twoCochain_skew a y]; rw [h x y z]
    abel

end LieModule.Cohomology
