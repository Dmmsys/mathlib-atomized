/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.IdealOperations

/-!
# Trivial Lie modules and Abelian Lie algebras

The action of a Lie algebra `L` on a module `M` is trivial if `⁅x, m⁆ = 0` for all `x ∈ L` and
`m ∈ M`. In the special case that `M = L` with the adjoint action, triviality corresponds to the
concept of an Abelian Lie algebra.

In this file we define these concepts and provide some related definitions and results.

## Main definitions

  * `LieModule.IsTrivial`
  * `IsLieAbelian`
  * `isMulCommutative_iff_isLieAbelian`
  * `LieModule.ker`
  * `LieModule.maxTrivSubmodule`
  * `LieAlgebra.center`

## Tags

lie algebra, abelian, commutative, center
-/

@[expose] public section


universe u v w w₁ w₂

/--
Definition of `LieModule.IsTrivial` / `LieModule.IsTrivial` 的定义

English:
class LieModule.IsTrivial
  parameters: (L : Type v) (M : Type w) [Bracket L M] [Zero M]
  axioms and operations (1):
    - trivial : forall (x : L) (m : M), ⁅x, m⁆ = 0

中文:
类 LieModule.IsTrivial
  参数: (L : 类型v) (M : Type w) [Bracket L M] [Zero M]
  公理与运算 (1 个):
    - trivial : 对任意 (x : L) (m : M), ⁅x, m⁆ = 0
-/
class LieModule.IsTrivial (L : Type v) (M : Type w) [Bracket L M] [Zero M] : Prop where
  trivial : forall (x : L) (m : M), ⁅x, m⁆ = 0

/--
theorem `trivial_lie_zero` / 定理 `trivial_lie_zero`

English:
theorem trivial_lie_zero
  statement: (L : Type v) (M : Type w) [Bracket L M] [Zero M] [LieModule.IsTrivial L M]
  proof: LieModule.IsTrivial.trivial x m

中文:
定理 trivial_lie_zero
  结论: (L : 类型v) (M : Type w) [Bracket L M] [Zero M] [LieModule.IsTrivial L M]
  证明: LieModule.IsTrivial.trivial x m

Depends on / 依赖: IsTrivial, LieModule, LieModule.IsTrivial.trivial
-/
theorem trivial_lie_zero (L : Type v) (M : Type w) [Bracket L M] [Zero M] [LieModule.IsTrivial L M]
    (x : L) (m : M) : ⁅x, m⁆ = 0 :=
  LieModule.IsTrivial.trivial x m

/--
Instance `LieModule.instIsTrivialOfSubsingleton` / 实例 `LieModule.instIsTrivialOfSubsingleton`

English:
instance LieModule.instIsTrivialOfSubsingleton
  signature: {L M : Type*}
  body: ⟨fun x m => by rw [Subsingleton.eq_zero x, zero_lie]⟩

中文:
实例 LieModule.instIsTrivialOfSubsingleton
  签名: {L M : 类型}
  定义体: ⟨fun x m => by rw [Subsingleton.eq_zero x, zero_lie]⟩

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, zero_lie
-/
instance LieModule.instIsTrivialOfSubsingleton {L M : Type*}
    [LieRing L] [AddCommGroup M] [LieRingModule L M] [Subsingleton L] : LieModule.IsTrivial L M :=
  ⟨fun x m => by rw [Subsingleton.eq_zero x, zero_lie]⟩

/--
Instance `LieModule.instIsTrivialOfSubsingleton'` / 实例 `LieModule.instIsTrivialOfSubsingleton'`

English:
instance LieModule.instIsTrivialOfSubsingleton'
  signature: {L M : Type*}
  body: ⟨fun x m => by simp_rw [Subsingleton.eq_zero m, lie_zero]⟩

中文:
实例 LieModule.instIsTrivialOfSubsingleton'
  签名: {L M : 类型}
  定义体: ⟨fun x m => by simp_rw [Subsingleton.eq_zero m, lie_zero]⟩

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, lie_zero, simp_rw
-/
instance LieModule.instIsTrivialOfSubsingleton' {L M : Type*}
    [LieRing L] [AddCommGroup M] [LieRingModule L M] [Subsingleton M] : LieModule.IsTrivial L M :=
  ⟨fun x m => by simp_rw [Subsingleton.eq_zero m, lie_zero]⟩

/--
Definition of `IsLieAbelian` / `IsLieAbelian` 的定义

English:
abbreviation IsLieAbelian
  signature: (L : Type v) [Bracket L L] [Zero L]
  body: LieModule.IsTrivial L L

中文:
缩写 IsLieAbelian
  签名: (L : 类型v) [Bracket L L] [Zero L]
  定义体: LieModule.IsTrivial L L

Depends on / 依赖: IsTrivial, LieModule, LieModule.IsTrivial
-/
abbrev IsLieAbelian (L : Type v) [Bracket L L] [Zero L] : Prop :=
  LieModule.IsTrivial L L

/--
Instance `LieIdeal.isLieAbelian_of_trivial` / 实例 `LieIdeal.isLieAbelian_of_trivial`

English:
instance LieIdeal.isLieAbelian_of_trivial
  signature: (R : Type u) (L : Type v) [CommRing R] [LieRing L]
  body: by apply h.trivial

中文:
实例 LieIdeal.isLieAbelian_of_trivial
  签名: (R : 类型u) (L : 类型v) [CommRing R] [LieRing L]
  定义体: by apply h.trivial

Depends on / 依赖: h.trivial
-/
instance LieIdeal.isLieAbelian_of_trivial (R : Type u) (L : Type v) [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) [h : LieModule.IsTrivial L I] : IsLieAbelian I where
  trivial x y := by apply h.trivial

/--
theorem `Function.Injective.isLieAbelian` / 定理 `Function.Injective.isLieAbelian`

English:
theorem Function.Injective.isLieAbelian
  statement: {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
  proof: { trivial := fun x y => h₁ <|
      calc
        f ⁅x, y⁆ = ⁅f x, f y⁆ := LieHom.map_lie f x y
        _ = 0 := trivial_lie_zero _ _ _ _
        _ = f 0 := (map_zero _).symm }

中文:
定理 Function.Injective.isLieAbelian
  结论: {R : 类型u} {L₁ : 类型v} {L₂ : Type w} [CommRing R]
  证明: { trivial := fun x y => h₁ <|
      calc
        f ⁅x, y⁆ = ⁅f x, f y⁆ := LieHom.map_lie f x y
        _ = 0 := trivial_lie_zero _ _ _ _
        _ = f 0 := (map_zero _).symm }

Depends on / 依赖: LieHom, LieHom.map_lie, map_lie, map_zero, trivial_lie_zero
-/
theorem Function.Injective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ ->ₗ⁅R⁆ L₂}
    (h₁ : Function.Injective f) (_ : IsLieAbelian L₂) : IsLieAbelian L₁ :=
  { trivial := fun x y => h₁ <|
      calc
        f ⁅x, y⁆ = ⁅f x, f y⁆ := LieHom.map_lie f x y
        _ = 0 := trivial_lie_zero _ _ _ _
        _ = f 0 := (map_zero _).symm }

/--
theorem `Function.Surjective.isLieAbelian` / 定理 `Function.Surjective.isLieAbelian`

English:
theorem Function.Surjective.isLieAbelian
  statement: {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
  proof: { trivial := fun x y => by
      obtain ⟨u, rfl⟩ := h₁ x
      obtain ⟨v, rfl⟩ := h₁ y
      rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero] }

中文:
定理 Function.Surjective.isLieAbelian
  结论: {R : 类型u} {L₁ : 类型v} {L₂ : Type w} [CommRing R]
  证明: { trivial := fun x y => by
      obtain ⟨u, rfl⟩ := h₁ x
      obtain ⟨v, rfl⟩ := h₁ y
      rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero] }

Depends on / 依赖: LieHom, LieHom.map_lie, map_lie, map_zero, trivial_lie_zero
-/
theorem Function.Surjective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ ->ₗ⁅R⁆ L₂}
    (h₁ : Function.Surjective f) (h₂ : IsLieAbelian L₁) : IsLieAbelian L₂ :=
  { trivial := fun x y => by
      obtain ⟨u, rfl⟩ := h₁ x
      obtain ⟨v, rfl⟩ := h₁ y
      rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero] }

/--
theorem `lie_abelian_iff_equiv_lie_abelian` / 定理 `lie_abelian_iff_equiv_lie_abelian`

English:
theorem lie_abelian_iff_equiv_lie_abelian
  statement: {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
  proof: ⟨e.symm.injective.isLieAbelian, e.injective.isLieAbelian⟩

中文:
定理 lie_abelian_iff_equiv_lie_abelian
  结论: {R : 类型u} {L₁ : 类型v} {L₂ : Type w} [CommRing R]
  证明: ⟨e.symm.injective.isLieAbelian, e.injective.isLieAbelian⟩

Depends on / 依赖: e.injective.isLieAbelian, e.symm.injective.isLieAbelian, injective, isLieAbelian
-/
theorem lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂) :
    IsLieAbelian L₁ ↔ IsLieAbelian L₂ :=
  ⟨e.symm.injective.isLieAbelian, e.injective.isLieAbelian⟩

/--
theorem `isMulCommutative_iff_isLieAbelian` / 定理 `isMulCommutative_iff_isLieAbelian`

English:
theorem isMulCommutative_iff_isLieAbelian
  given: {A : Type v} [Ring A]
  proof: by
  have : IsLieAbelian A ↔ forall a b : A, ⁅a, b⁆ = 0 := ⟨(·.trivial), (⟨·⟩)⟩
  simp [this, isMulCommutative_iff, LieRing.of_associative_ring_bracket, sub_eq_zero]

@[deprecated (since := "2026-04-01")]
alias commutative_ring_iff_abelian_lie_ring := isMulCommutative_iff_isLieAbelian

中文:
定理 isMulCommutative_iff_isLieAbelian
  条件: {A : 类型v} [Ring A]
  证明: by
  have : IsLieAbelian A ↔ forall a b : A, ⁅a, b⁆ = 0 := ⟨(·.trivial), (⟨·⟩)⟩
  simp [this, isMulCommutative_iff, LieRing.of_associative_ring_bracket, sub_eq_zero]

@[deprecated (since := "2026-04-01")]
alias commutative_ring_iff_abelian_lie_ring := isMulCommutative_iff_isLieAbelian

Depends on / 依赖: IsLieAbelian, LieRing, LieRing.of_associative_ring_bracket, isMulCommutative_iff, of_associative_ring_bracket, sub_eq_zero
-/
theorem isMulCommutative_iff_isLieAbelian {A : Type v} [Ring A] :
    IsMulCommutative A ↔ IsLieAbelian A := by
  have : IsLieAbelian A ↔ forall a b : A, ⁅a, b⁆ = 0 := ⟨(·.trivial), (⟨·⟩)⟩
  simp [this, isMulCommutative_iff, LieRing.of_associative_ring_bracket, sub_eq_zero]

@[deprecated (since := "2026-04-01")]
alias commutative_ring_iff_abelian_lie_ring := isMulCommutative_iff_isLieAbelian

/--
theorem `LieSubalgebra.isLieAbelian_lieSpan_iff` / 定理 `LieSubalgebra.isLieAbelian_lieSpan_iff`

English:
theorem LieSubalgebra.isLieAbelian_lieSpan_iff
  proof: by
  refine ⟨fun h x hx y hy => ?_, fun h => ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩⟩
  · let x' : lieSpan R L s := ⟨x, subset_lieSpan hx⟩
    let y' : lieSpan R L s := ⟨y, subset_lieSpan hy⟩
    suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
    simp [trivial_lie_zero]
  · induction hx usi

中文:
定理 LieSubalgebra.isLieAbelian_lieSpan_iff
  证明: by
  refine ⟨fun h x hx y hy => ?_, fun h => ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩⟩
  · let x' : lieSpan R L s := ⟨x, subset_lieSpan hx⟩
    let y' : lieSpan R L s := ⟨y, subset_lieSpan hy⟩
    suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
    simp [trivial_lie_zero]
  · induction hx usi
-/
@[simp] theorem LieSubalgebra.isLieAbelian_lieSpan_iff
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {s : Set L} :
    IsLieAbelian (lieSpan R L s) ↔ forallᵉ (x in s) (y in s), ⁅x, y⁆ = 0 := by
  refine ⟨fun h x hx y hy => ?_, fun h => ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩⟩
  · let x' : lieSpan R L s := ⟨x, subset_lieSpan hx⟩
    let y' : lieSpan R L s := ⟨y, subset_lieSpan hy⟩
    suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
    simp [trivial_lie_zero]
  · induction hx using lieSpan_induction with
    | mem w hw =>
      induction hy using lieSpan_induction with
      | mem u hu => simpa [Subtype.ext_iff] using h w hw u hu
      | zero => simp [Subtype.ext_iff]
      | add u v _ _ hu hv =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero, lie_add] at hu hv ⊢
        simp [hu, hv]
      | smul t u _ hu =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu
        simp [Subtype.ext_iff, hu]
      | lie u v _ _ hu hv =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu hv ⊢
        rw [leibniz_lie]
        simp [hu, hv]
    | zero => simp [Subtype.ext_iff]
    | add u v _ _ hu hv =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero, add_lie] at hu hv ⊢
      simp [hu, hv]
    | smul t u _ hu =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu
      simp [Subtype.ext_iff, hu]
    | lie u v _ _ hu hv =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu hv ⊢
      simp [hu, hv]

section Center

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : LieIdeal R L
  body: (toEnd R L M).ker

@[simp]

中文:
定义 ker
  签名: : LieIdeal R L
  定义体: (toEnd R L M).ker

@[simp]
-/
protected def ker : LieIdeal R L :=
  (toEnd R L M).ker

@[simp]
/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: (x : L)
  statement: x in LieModule.ker R L M ↔ forall m : M, ⁅x, m⁆ = 0
  proof: by
  simp only [LieModule.ker, LieHom.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    toEnd_apply_apply]

中文:
定理 mem_ker
  条件: (x : L)
  结论: x in LieModule.ker R L M ↔ 对任意 m : M, ⁅x, m⁆ = 0
  证明: by
  simp only [LieModule.ker, LieHom.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    toEnd_apply_apply]
-/
protected theorem mem_ker (x : L) : x in LieModule.ker R L M ↔ forall m : M, ⁅x, m⁆ = 0 := by
  simp only [LieModule.ker, LieHom.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    toEnd_apply_apply]

/--
lemma `_root_.LieIdeal.isLieAbelian_iff` / 引理 `_root_.LieIdeal.isLieAbelian_iff`

English:
lemma _root_.LieIdeal.isLieAbelian_iff
  given: {I : LieIdeal R L}
  proof: by
  refine ⟨fun hI x hx => LieHom.mem_ker.mpr ?_, fun h => ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩⟩
  · ext y
    have := IsTrivial.trivial (⟨x, hx⟩ : I) y
    rw [LieIdeal.coe_bracket_of_module] at this
    simp [this]
  · simpa using LinearMap.congr_fun (h hx) ⟨y, hy⟩

中文:
引理 _root_.LieIdeal.isLieAbelian_iff
  条件: {I : LieIdeal R L}
  证明: by
  refine ⟨fun hI x hx => LieHom.mem_ker.mpr ?_, fun h => ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩⟩
  · ext y
    have := IsTrivial.trivial (⟨x, hx⟩ : I) y
    rw [LieIdeal.coe_bracket_of_module] at this
    simp [this]
  · simpa using LinearMap.congr_fun (h hx) ⟨y, hy⟩

Depends on / 依赖: IsTrivial, IsTrivial.trivial, LieHom, LieHom.mem_ker.mpr, LieIdeal, LieIdeal.coe_bracket_of_module, LinearMap, LinearMap.congr_fun, coe_bracket_of_module, congr_fun, mem_ker
-/
lemma _root_.LieIdeal.isLieAbelian_iff {I : LieIdeal R L} :
    IsLieAbelian I ↔ I <= LieModule.ker R L I := by
  refine ⟨fun hI x hx => LieHom.mem_ker.mpr ?_, fun h => ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩⟩
  · ext y
    have := IsTrivial.trivial (⟨x, hx⟩ : I) y
    rw [LieIdeal.coe_bracket_of_module] at this
    simp [this]
  · simpa using LinearMap.congr_fun (h hx) ⟨y, hy⟩

/--
lemma `isFaithful_iff_ker_eq_bot` / 引理 `isFaithful_iff_ker_eq_bot`

English:
lemma isFaithful_iff_ker_eq_bot
  statement: IsFaithful R L M ↔ LieModule.ker R L M = ⊥
  proof: by
  rw [isFaithful_iff']; rw [LieSubmodule.ext_iff]
  aesop

中文:
引理 isFaithful_iff_ker_eq_bot
  结论: IsFaithful R L M ↔ LieModule.ker R L M = ⊥
  证明: by
  rw [isFaithful_iff']; rw [LieSubmodule.ext_iff]
  aesop

Depends on / 依赖: LieSubmodule, LieSubmodule.ext_iff, ext_iff, isFaithful_iff
-/
lemma isFaithful_iff_ker_eq_bot : IsFaithful R L M ↔ LieModule.ker R L M = ⊥ := by
  rw [isFaithful_iff']; rw [LieSubmodule.ext_iff]
  aesop

/--
lemma `ker_eq_bot` / 引理 `ker_eq_bot`

English:
lemma ker_eq_bot
  given: [IsFaithful R L M]
  proof: (isFaithful_iff_ker_eq_bot R L M).mp inferInstance

中文:
引理 ker_eq_bot
  条件: [IsFaithful R L M]
  证明: (isFaithful_iff_ker_eq_bot R L M).mp inferInstance
-/
@[simp] lemma ker_eq_bot [IsFaithful R L M] :
    LieModule.ker R L M = ⊥ :=
  (isFaithful_iff_ker_eq_bot R L M).mp inferInstance

/--
Definition of `maxTrivSubmodule` / `maxTrivSubmodule` 的定义

English:
definition maxTrivSubmodule
  signature: : LieSubmodule R L M where
  body: { m | forall x : L, ⁅x, m⁆ = 0 }
  zero_mem' x := lie_zero x
  add_mem' {x y} hx hy z := by rw [lie_add, hx, hy, add_zero]
  smul_mem' c x hx y := by rw [lie_smul, hx, smul_zero]
  lie_mem {x m} hm y := by rw [hm, lie_zero]

@[simp]

中文:
定义 maxTrivSubmodule
  签名: : LieSubmodule R L M where
  定义体: { m | forall x : L, ⁅x, m⁆ = 0 }
  zero_mem' x := lie_zero x
  add_mem' {x y} hx hy z := by rw [lie_add, hx, hy, add_zero]
  smul_mem' c x hx y := by rw [lie_smul, hx, smul_zero]
  lie_mem {x m} hm y := by rw [hm, lie_zero]

@[simp]
-/
def maxTrivSubmodule : LieSubmodule R L M where
  carrier := { m | forall x : L, ⁅x, m⁆ = 0 }
  zero_mem' x := lie_zero x
  add_mem' {x y} hx hy z := by rw [lie_add, hx, hy, add_zero]
  smul_mem' c x hx y := by rw [lie_smul, hx, smul_zero]
  lie_mem {x m} hm y := by rw [hm, lie_zero]

@[simp]
/--
theorem `mem_maxTrivSubmodule` / 定理 `mem_maxTrivSubmodule`

English:
theorem mem_maxTrivSubmodule
  given: (m : M)
  statement: m in maxTrivSubmodule R L M ↔ forall x : L, ⁅x, m⁆ = 0
  proof: Iff.rfl

中文:
定理 mem_maxTrivSubmodule
  条件: (m : M)
  结论: m in maxTrivSubmodule R L M ↔ 对任意 x : L, ⁅x, m⁆ = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_maxTrivSubmodule (m : M) : m in maxTrivSubmodule R L M ↔ forall x : L, ⁅x, m⁆ = 0 :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrivial L (maxTrivSubmodule R L M)
  body: Subtype.ext (m.property x)

@[simp]

中文:
实例 :
  签名: IsTrivial L (maxTrivSubmodule R L M)
  定义体: Subtype.ext (m.property x)

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, m.property, property
-/
instance : IsTrivial L (maxTrivSubmodule R L M) where trivial x m := Subtype.ext (m.property x)

@[simp]
/--
theorem `ideal_oper_maxTrivSubmodule_eq_bot` / 定理 `ideal_oper_maxTrivSubmodule_eq_bot`

English:
theorem ideal_oper_maxTrivSubmodule_eq_bot
  given: (I : LieIdeal R L)
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.bot_toSubmodule]; rw [Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x

中文:
定理 ideal_oper_maxTrivSubmodule_eq_bot
  条件: (I : LieIdeal R L)
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.bot_toSubmodule]; rw [Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x

Depends on / 依赖: LieSubmodule, LieSubmodule.bot_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.toSubmodule_inj, Submodule, Submodule.span_eq_bot, bot_toSubmodule, lieIdeal_oper_eq_linear_span, span_eq_bot, toSubmodule_inj
-/
theorem ideal_oper_maxTrivSubmodule_eq_bot (I : LieIdeal R L) :
    ⁅I, maxTrivSubmodule R L M⁆ = ⊥ := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.bot_toSubmodule]; rw [Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x

/--
theorem `le_max_triv_iff_bracket_eq_bot` / 定理 `le_max_triv_iff_bracket_eq_bot`

English:
theorem le_max_triv_iff_bracket_eq_bot
  given: {N : LieSubmodule R L M}
  proof: by
  refine ⟨fun h => ?_, fun h m hm => ?_⟩
  · rw [← le_bot_iff, ← ideal_oper_maxTrivSubmodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right ⊤ h
  · rw [mem_maxTrivSubmodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm

中文:
定理 le_max_triv_iff_bracket_eq_bot
  条件: {N : LieSubmodule R L M}
  证明: by
  refine ⟨fun h => ?_, fun h m hm => ?_⟩
  · rw [← le_bot_iff, ← ideal_oper_maxTrivSubmodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right ⊤ h
  · rw [mem_maxTrivSubmodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_eq_bot_iff, LieSubmodule.mem_top, LieSubmodule.mono_lie_right, ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff, lie_eq_bot_iff, mem_maxTrivSubmodule, mem_top, mono_lie_right
-/
theorem le_max_triv_iff_bracket_eq_bot {N : LieSubmodule R L M} :
    N <= maxTrivSubmodule R L M ↔ ⁅(⊤ : LieIdeal R L), N⁆ = ⊥ := by
  refine ⟨fun h => ?_, fun h m hm => ?_⟩
  · rw [← le_bot_iff, ← ideal_oper_maxTrivSubmodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right ⊤ h
  · rw [mem_maxTrivSubmodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm

/--
theorem `trivial_iff_le_maximal_trivial` / 定理 `trivial_iff_le_maximal_trivial`

English:
theorem trivial_iff_le_maximal_trivial
  given: (N : LieSubmodule R L M)
  proof: ⟨fun h m hm x => IsTrivial.casesOn h fun h => Subtype.ext_iff.mp (h x ⟨m, hm⟩), fun h =>
    { trivial := fun x m => Subtype.ext (h m.2 x) }⟩

中文:
定理 trivial_iff_le_maximal_trivial
  条件: (N : LieSubmodule R L M)
  证明: ⟨fun h m hm x => IsTrivial.casesOn h fun h => Subtype.ext_iff.mp (h x ⟨m, hm⟩), fun h =>
    { trivial := fun x m => Subtype.ext (h m.2 x) }⟩

Depends on / 依赖: IsTrivial, IsTrivial.casesOn, Subtype, Subtype.ext, Subtype.ext_iff.mp, casesOn, ext_iff
-/
theorem trivial_iff_le_maximal_trivial (N : LieSubmodule R L M) :
    IsTrivial L N ↔ N <= maxTrivSubmodule R L M :=
  ⟨fun h m hm x => IsTrivial.casesOn h fun h => Subtype.ext_iff.mp (h x ⟨m, hm⟩), fun h =>
    { trivial := fun x m => Subtype.ext (h m.2 x) }⟩

/--
theorem `isTrivial_iff_max_triv_eq_top` / 定理 `isTrivial_iff_max_triv_eq_top`

English:
theorem isTrivial_iff_max_triv_eq_top
  statement: IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤
  proof: by
  constructor
  · rintro ⟨h⟩; ext; simp only [mem_maxTrivSubmodule, h, forall_const, LieSubmodule.mem_top]
  · intro h; constructor; intro x m; revert x
    rw [← mem_maxTrivSubmodule R L M]; rw [h]; exact LieSubmodule.mem_top m

中文:
定理 isTrivial_iff_max_triv_eq_top
  结论: IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤
  证明: by
  constructor
  · rintro ⟨h⟩; ext; simp only [mem_maxTrivSubmodule, h, forall_const, LieSubmodule.mem_top]
  · intro h; constructor; intro x m; revert x
    rw [← mem_maxTrivSubmodule R L M]; rw [h]; exact LieSubmodule.mem_top m

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_top, forall_const, mem_maxTrivSubmodule, mem_top, revert
-/
theorem isTrivial_iff_max_triv_eq_top : IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤ := by
  constructor
  · rintro ⟨h⟩; ext; simp only [mem_maxTrivSubmodule, h, forall_const, LieSubmodule.mem_top]
  · intro h; constructor; intro x m; revert x
    rw [← mem_maxTrivSubmodule R L M]; rw [h]; exact LieSubmodule.mem_top m

variable {R L M N}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `maxTrivHom` / `maxTrivHom` 的定义

English:
definition maxTrivHom
  signature: (f : M ->ₗ⁅R,L⁆ N)
  body: ⟨f m, fun x =>
(LieModuleHom.map_lie _ _ _).symm.trans
      (congr_arg f (m.property x)).trans (map_zero _)⟩
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp
  map_lie' {x m} := by simp [trivial_lie_zero]

@[norm_cast, simp]

中文:
定义 maxTrivHom
  签名: (f : M ->ₗ⁅R,L⁆ N)
  定义体: ⟨f m, fun x =>
(LieModuleHom.map_lie _ _ _).symm.trans
      (congr_arg f (m.property x)).trans (map_zero _)⟩
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp
  map_lie' {x m} := by simp [trivial_lie_zero]

@[norm_cast, simp]
-/
def maxTrivHom (f : M ->ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ->ₗ⁅R,L⁆ maxTrivSubmodule R L N where
  toFun m := ⟨f m, fun x =>
(LieModuleHom.map_lie _ _ _).symm.trans
      (congr_arg f (m.property x)).trans (map_zero _)⟩
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp
  map_lie' {x m} := by simp [trivial_lie_zero]

@[norm_cast, simp]
/--
theorem `coe_maxTrivHom_apply` / 定理 `coe_maxTrivHom_apply`

English:
theorem coe_maxTrivHom_apply
  given: (f : M ->ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M)
  proof: rfl

中文:
定理 coe_maxTrivHom_apply
  条件: (f : M ->ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M)
  证明: rfl
-/
theorem coe_maxTrivHom_apply (f : M ->ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) :
    (maxTrivHom f m : N) = f m :=
  rfl

/--
Definition of `maxTrivEquiv` / `maxTrivEquiv` 的定义

English:
definition maxTrivEquiv
  signature: (e : M ≃ₗ⁅R,L⁆ N)
  body: { maxTrivHom (e : M ->ₗ⁅R,L⁆ N) with
    toFun := maxTrivHom (e : M ->ₗ⁅R,L⁆ N)
    invFun := maxTrivHom (e.symm : N ->ₗ⁅R,L⁆ M)
    left_inv := fun m => by ext; simp
    right_inv := fun n => by ext; simp }

@[norm_cast, simp]

中文:
定义 maxTrivEquiv
  签名: (e : M ≃ₗ⁅R,L⁆ N)
  定义体: { maxTrivHom (e : M ->ₗ⁅R,L⁆ N) with
    toFun := maxTrivHom (e : M ->ₗ⁅R,L⁆ N)
    invFun := maxTrivHom (e.symm : N ->ₗ⁅R,L⁆ M)
    left_inv := fun m => by ext; simp
    right_inv := fun n => by ext; simp }

@[norm_cast, simp]

Depends on / 依赖: e.symm, invFun, left_inv, maxTrivHom, right_inv
-/
def maxTrivEquiv (e : M ≃ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ≃ₗ⁅R,L⁆ maxTrivSubmodule R L N :=
  { maxTrivHom (e : M ->ₗ⁅R,L⁆ N) with
    toFun := maxTrivHom (e : M ->ₗ⁅R,L⁆ N)
    invFun := maxTrivHom (e.symm : N ->ₗ⁅R,L⁆ M)
    left_inv := fun m => by ext; simp
    right_inv := fun n => by ext; simp }

@[norm_cast, simp]
/--
theorem `coe_maxTrivEquiv_apply` / 定理 `coe_maxTrivEquiv_apply`

English:
theorem coe_maxTrivEquiv_apply
  given: (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M)
  proof: rfl

@[simp]

中文:
定理 coe_maxTrivEquiv_apply
  条件: (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M)
  证明: rfl

@[simp]
-/
theorem coe_maxTrivEquiv_apply (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) :
    (maxTrivEquiv e m : N) = e ↑m :=
  rfl

@[simp]
/--
theorem `maxTrivEquiv_of_refl_eq_refl` / 定理 `maxTrivEquiv_of_refl_eq_refl`

English:
theorem maxTrivEquiv_of_refl_eq_refl
  proof: by
  ext; simp only [coe_maxTrivEquiv_apply, LieModuleEquiv.refl_apply]

@[simp]

中文:
定理 maxTrivEquiv_of_refl_eq_refl
  证明: by
  ext; simp only [coe_maxTrivEquiv_apply, LieModuleEquiv.refl_apply]

@[simp]

Depends on / 依赖: LieModuleEquiv, LieModuleEquiv.refl_apply, coe_maxTrivEquiv_apply, refl_apply
-/
theorem maxTrivEquiv_of_refl_eq_refl :
    maxTrivEquiv (LieModuleEquiv.refl : M ≃ₗ⁅R,L⁆ M) = LieModuleEquiv.refl := by
  ext; simp only [coe_maxTrivEquiv_apply, LieModuleEquiv.refl_apply]

@[simp]
/--
theorem `maxTrivEquiv_of_equiv_symm_eq_symm` / 定理 `maxTrivEquiv_of_equiv_symm_eq_symm`

English:
theorem maxTrivEquiv_of_equiv_symm_eq_symm
  given: (e : M ≃ₗ⁅R,L⁆ N)
  proof: rfl

中文:
定理 maxTrivEquiv_of_equiv_symm_eq_symm
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  证明: rfl
-/
theorem maxTrivEquiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) :
    (maxTrivEquiv e).symm = maxTrivEquiv e.symm :=
  rfl

/--
Definition of `maxTrivLinearMapEquivLieModuleHom` / `maxTrivLinearMapEquivLieModuleHom` 的定义

English:
definition maxTrivLinearMapEquivLieModuleHom
  signature: : maxTrivSubmodule R L (M ->ₗ[R] N) ≃ₗ[R] M ->ₗ⁅R,L⁆ N where
  body: { toLinearMap := f.val
      map_lie' := fun {x m} => by
        have hf : ⁅x, f.val⁆ m = 0 := by rw [f.property x, LinearMap.zero_apply]
        rw [LieHom.lie_apply]; rw [sub_eq_zero]; rw [← LinearMap.toFun_eq_coe] at hf; exact hf.symm }
  map_add' f g := by ext; simp
  map_smul' F G := by ext; si

中文:
定义 maxTrivLinearMapEquivLieModuleHom
  签名: : maxTrivSubmodule R L (M ->ₗ[R] N) ≃ₗ[R] M ->ₗ⁅R,L⁆ N where
  定义体: { toLinearMap := f.val
      map_lie' := fun {x m} => by
        have hf : ⁅x, f.val⁆ m = 0 := by rw [f.property x, LinearMap.zero_apply]
        rw [LieHom.lie_apply]; rw [sub_eq_zero]; rw [← LinearMap.toFun_eq_coe] at hf; exact hf.symm }
  map_add' f g := by ext; simp
  map_smul' F G := by ext; si

Depends on / 依赖: LieHom, LieHom.lie_apply, LinearMap, LinearMap.toFun_eq_coe, LinearMap.zero_apply, f.property, f.val, hf.symm, invFun, left_inv, lie_apply, map_add, map_lie, map_smul, property, right_inv, sub_eq_zero, toFun_eq_coe, toLinearMap, zero_apply
-/
def maxTrivLinearMapEquivLieModuleHom : maxTrivSubmodule R L (M ->ₗ[R] N) ≃ₗ[R] M ->ₗ⁅R,L⁆ N where
  toFun f :=
    { toLinearMap := f.val
      map_lie' := fun {x m} => by
        have hf : ⁅x, f.val⁆ m = 0 := by rw [f.property x, LinearMap.zero_apply]
        rw [LieHom.lie_apply]; rw [sub_eq_zero]; rw [← LinearMap.toFun_eq_coe] at hf; exact hf.symm }
  map_add' f g := by ext; simp
  map_smul' F G := by ext; simp
  invFun F := ⟨F, fun x => by ext; simp⟩
  left_inv f := by simp
  right_inv F := by simp

@[simp]
/--
theorem `coe_maxTrivLinearMapEquivLieModuleHom` / 定理 `coe_maxTrivLinearMapEquivLieModuleHom`

English:
theorem coe_maxTrivLinearMapEquivLieModuleHom
  given: (f : maxTrivSubmodule R L (M ->ₗ[R] N))
  proof: by ext; rfl

@[simp]

中文:
定理 coe_maxTrivLinearMapEquivLieModuleHom
  条件: (f : maxTrivSubmodule R L (M ->ₗ[R] N))
  证明: by ext; rfl

@[simp]
-/
theorem coe_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M ->ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) f : M -> N) = f := by ext; rfl

@[simp]
/--
theorem `coe_maxTrivLinearMapEquivLieModuleHom_symm` / 定理 `coe_maxTrivLinearMapEquivLieModuleHom_symm`

English:
theorem coe_maxTrivLinearMapEquivLieModuleHom_symm
  given: (f : M ->ₗ⁅R,L⁆ N)
  proof: rfl

@[simp]

中文:
定理 coe_maxTrivLinearMapEquivLieModuleHom_symm
  条件: (f : M ->ₗ⁅R,L⁆ N)
  证明: rfl

@[simp]
-/
theorem coe_maxTrivLinearMapEquivLieModuleHom_symm (f : M ->ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) |>.symm f : M -> N) = f :=
  rfl

@[simp]
/--
theorem `toLinearMap_maxTrivLinearMapEquivLieModuleHom` / 定理 `toLinearMap_maxTrivLinearMapEquivLieModuleHom`

English:
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom
  given: (f : maxTrivSubmodule R L (M ->ₗ[R] N))
  proof: by
  ext; rfl

@[simp]

中文:
定理 toLinearMap_maxTrivLinearMapEquivLieModuleHom
  条件: (f : maxTrivSubmodule R L (M ->ₗ[R] N))
  证明: by
  ext; rfl

@[simp]
-/
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M ->ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) f : M ->ₗ[R] N) = (f : M ->ₗ[R] N) := by
  ext; rfl

@[simp]
/--
theorem `toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm` / 定理 `toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm`

English:
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm
  given: (f : M ->ₗ⁅R,L⁆ N)
  proof: rfl

中文:
定理 toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm
  条件: (f : M ->ₗ⁅R,L⁆ N)
  证明: rfl
-/
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm (f : M ->ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) |>.symm f : M ->ₗ[R] N) = (f : M ->ₗ[R] N) :=
  rfl

end LieModule

namespace LieAlgebra

/--
Definition of `center` / `center` 的定义

English:
abbreviation center
  signature: : LieIdeal R L
  body: LieModule.maxTrivSubmodule R L L

中文:
缩写 center
  签名: : LieIdeal R L
  定义体: LieModule.maxTrivSubmodule R L L

Depends on / 依赖: LieModule, LieModule.maxTrivSubmodule, maxTrivSubmodule
-/
abbrev center : LieIdeal R L :=
  LieModule.maxTrivSubmodule R L L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLieAbelian (center R L)
  body: inferInstance

中文:
实例 :
  签名: IsLieAbelian (center R L)
  定义体: inferInstance
-/
instance : IsLieAbelian (center R L) :=
  inferInstance

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp]
/--
theorem `ad_ker_eq_self_module_ker` / 定理 `ad_ker_eq_self_module_ker`

English:
theorem ad_ker_eq_self_module_ker
  statement: (ad R L).ker = LieModule.ker R L L
  proof: rfl

@[simp]

中文:
定理 ad_ker_eq_self_module_ker
  结论: (ad R L).ker = LieModule.ker R L L
  证明: rfl

@[simp]
-/
theorem ad_ker_eq_self_module_ker : (ad R L).ker = LieModule.ker R L L :=
  rfl

@[simp]
/--
theorem `self_module_ker_eq_center` / 定理 `self_module_ker_eq_center`

English:
theorem self_module_ker_eq_center
  statement: LieModule.ker R L L = center R L
  proof: by
  ext y
  simp only [LieModule.mem_maxTrivSubmodule, LieModule.mem_ker, ← lie_skew _ y, neg_eq_zero]

中文:
定理 self_module_ker_eq_center
  结论: LieModule.ker R L L = center R L
  证明: by
  ext y
  simp only [LieModule.mem_maxTrivSubmodule, LieModule.mem_ker, ← lie_skew _ y, neg_eq_zero]

Depends on / 依赖: LieModule, LieModule.mem_ker, LieModule.mem_maxTrivSubmodule, lie_skew, mem_ker, mem_maxTrivSubmodule, neg_eq_zero
-/
theorem self_module_ker_eq_center : LieModule.ker R L L = center R L := by
  ext y
  simp only [LieModule.mem_maxTrivSubmodule, LieModule.mem_ker, ← lie_skew _ y, neg_eq_zero]

/--
theorem `abelian_of_le_center` / 定理 `abelian_of_le_center`

English:
theorem abelian_of_le_center
  given: (I : LieIdeal R L) (h : I <= center R L)
  statement: IsLieAbelian I
  proof: haveI : LieModule.IsTrivial L I := (LieModule.trivial_iff_le_maximal_trivial R L L I).mpr h
  LieIdeal.isLieAbelian_of_trivial R L I

中文:
定理 abelian_of_le_center
  条件: (I : LieIdeal R L) (h : I <= center R L)
  结论: IsLieAbelian I
  证明: haveI : LieModule.IsTrivial L I := (LieModule.trivial_iff_le_maximal_trivial R L L I).mpr h
  LieIdeal.isLieAbelian_of_trivial R L I

Depends on / 依赖: IsTrivial, LieIdeal, LieIdeal.isLieAbelian_of_trivial, LieModule, LieModule.IsTrivial, LieModule.trivial_iff_le_maximal_trivial, isLieAbelian_of_trivial, trivial_iff_le_maximal_trivial
-/
theorem abelian_of_le_center (I : LieIdeal R L) (h : I <= center R L) : IsLieAbelian I :=
  haveI : LieModule.IsTrivial L I := (LieModule.trivial_iff_le_maximal_trivial R L L I).mpr h
  LieIdeal.isLieAbelian_of_trivial R L I

/--
theorem `isLieAbelian_iff_center_eq_top` / 定理 `isLieAbelian_iff_center_eq_top`

English:
theorem isLieAbelian_iff_center_eq_top
  statement: IsLieAbelian L ↔ center R L = ⊤
  proof: LieModule.isTrivial_iff_max_triv_eq_top R L L

中文:
定理 isLieAbelian_iff_center_eq_top
  结论: IsLieAbelian L ↔ center R L = ⊤
  证明: LieModule.isTrivial_iff_max_triv_eq_top R L L

Depends on / 依赖: LieModule, LieModule.isTrivial_iff_max_triv_eq_top, isTrivial_iff_max_triv_eq_top
-/
theorem isLieAbelian_iff_center_eq_top : IsLieAbelian L ↔ center R L = ⊤ :=
  LieModule.isTrivial_iff_max_triv_eq_top R L L

/--
theorem `isFaithful_self_iff` / 定理 `isFaithful_self_iff`

English:
theorem isFaithful_self_iff
  statement: LieModule.IsFaithful R L L ↔ center R L = ⊥
  proof: by
  rw [LieModule.isFaithful_iff_ker_eq_bot]; rw [self_module_ker_eq_center]

@[simp]

中文:
定理 isFaithful_self_iff
  结论: LieModule.IsFaithful R L L ↔ center R L = ⊥
  证明: by
  rw [LieModule.isFaithful_iff_ker_eq_bot]; rw [self_module_ker_eq_center]

@[simp]

Depends on / 依赖: LieModule, LieModule.isFaithful_iff_ker_eq_bot, isFaithful_iff_ker_eq_bot, self_module_ker_eq_center
-/
theorem isFaithful_self_iff : LieModule.IsFaithful R L L ↔ center R L = ⊥ := by
  rw [LieModule.isFaithful_iff_ker_eq_bot]; rw [self_module_ker_eq_center]

@[simp]
/--
theorem `center_eq_bot` / 定理 `center_eq_bot`

English:
theorem center_eq_bot
  given: [LieModule.IsFaithful R L L]
  proof: (isFaithful_self_iff R L).mp inferInstance

中文:
定理 center_eq_bot
  条件: [LieModule.IsFaithful R L L]
  证明: (isFaithful_self_iff R L).mp inferInstance

Depends on / 依赖: isFaithful_self_iff
-/
theorem center_eq_bot [LieModule.IsFaithful R L L] :
    center R L = ⊥ :=
  (isFaithful_self_iff R L).mp inferInstance

end LieAlgebra

namespace LieModule

variable {R L}
variable {x : L} (hx : x in LieAlgebra.center R L) (y : L)
include hx

attribute [local instance 100] LieRing.ofAssociativeRing

/--
lemma `commute_toEnd_of_mem_center_left` / 引理 `commute_toEnd_of_mem_center_left`

English:
lemma commute_toEnd_of_mem_center_left
  proof: by
  rw [Commute.symm_iff]; rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [hx y]; rw [map_zero]

中文:
引理 commute_toEnd_of_mem_center_left
  证明: by
  rw [Commute.symm_iff]; rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [hx y]; rw [map_zero]

Depends on / 依赖: Commute, Commute.symm_iff, LieHom, LieHom.map_lie, commute_iff_lie_eq, map_lie, map_zero, symm_iff
-/
lemma commute_toEnd_of_mem_center_left :
    Commute (toEnd R L M x) (toEnd R L M y) := by
  rw [Commute.symm_iff]; rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [hx y]; rw [map_zero]

/--
lemma `commute_toEnd_of_mem_center_right` / 引理 `commute_toEnd_of_mem_center_right`

English:
lemma commute_toEnd_of_mem_center_right
  proof: (LieModule.commute_toEnd_of_mem_center_left M hx y).symm

中文:
引理 commute_toEnd_of_mem_center_right
  证明: (LieModule.commute_toEnd_of_mem_center_left M hx y).symm

Depends on / 依赖: LieModule, LieModule.commute_toEnd_of_mem_center_left, commute_toEnd_of_mem_center_left
-/
lemma commute_toEnd_of_mem_center_right :
    Commute (toEnd R L M y) (toEnd R L M x) :=
  (LieModule.commute_toEnd_of_mem_center_left M hx y).symm

end LieModule

end Center

section IdealOperations

open LieSubmodule LieSubalgebra

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

@[simp]
/--
theorem `LieSubmodule.trivial_lie_oper_zero` / 定理 `LieSubmodule.trivial_lie_oper_zero`

English:
theorem LieSubmodule.trivial_lie_oper_zero
  given: [LieModule.IsTrivial L M]
  statement: ⁅I, N⁆ = ⊥
  proof: by
  suffices ⁅I, N⁆ <= ⊥ from le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  rintro m ⟨x, n, h⟩; rw [trivial_lie_zero] at h; simp [← h]

中文:
定理 LieSubmodule.trivial_lie_oper_zero
  条件: [LieModule.IsTrivial L M]
  结论: ⁅I, N⁆ = ⊥
  证明: by
  suffices ⁅I, N⁆ <= ⊥ from le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  rintro m ⟨x, n, h⟩; rw [trivial_lie_zero] at h; simp [← h]

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan_le, le_bot_iff, le_bot_iff.mp, lieIdeal_oper_eq_span, lieSpan_le, trivial_lie_zero
-/
theorem LieSubmodule.trivial_lie_oper_zero [LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥ := by
  suffices ⁅I, N⁆ <= ⊥ from le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  rintro m ⟨x, n, h⟩; rw [trivial_lie_zero] at h; simp [← h]

/--
theorem `LieSubmodule.lie_abelian_iff_lie_self_eq_bot` / 定理 `LieSubmodule.lie_abelian_iff_lie_self_eq_bot`

English:
theorem LieSubmodule.lie_abelian_iff_lie_self_eq_bot
  statement: IsLieAbelian I ↔ ⁅I, I⁆ = ⊥
  proof: by
  simp only [_root_.eq_bot_iff, lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le,
    LieSubmodule.bot_coe, Set.subset_singleton_iff, Set.mem_ofPred_eq, exists_imp]
  refine
    ⟨fun h z x y hz =>
      hz.symm.trans
        (((I : LieSubalgebra R L).coe_bracket x y).symm.trans
          ((coe_zero

中文:
定理 LieSubmodule.lie_abelian_iff_lie_self_eq_bot
  结论: IsLieAbelian I ↔ ⁅I, I⁆ = ⊥
  证明: by
  simp only [_root_.eq_bot_iff, lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le,
    LieSubmodule.bot_coe, Set.subset_singleton_iff, Set.mem_ofPred_eq, exists_imp]
  refine
    ⟨fun h z x y hz =>
      hz.symm.trans
        (((I : LieSubalgebra R L).coe_bracket x y).symm.trans
          ((coe_zero

Depends on / 依赖: LieSubalgebra, LieSubmodule, LieSubmodule.bot_coe, LieSubmodule.lieSpan_le, Set.mem_ofPred_eq, Set.subset_singleton_iff, _root_, _root_.eq_bot_iff, bot_coe, coe_bracket, coe_zero_iff_zero, eq_bot_iff, exists_imp, h.trivial, hz.symm.trans, lieIdeal_oper_eq_span, lieSpan_le, mem_ofPred_eq, subset_singleton_iff, symm.trans
-/
theorem LieSubmodule.lie_abelian_iff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥ := by
  simp only [_root_.eq_bot_iff, lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le,
    LieSubmodule.bot_coe, Set.subset_singleton_iff, Set.mem_ofPred_eq, exists_imp]
  refine
    ⟨fun h z x y hz =>
      hz.symm.trans
        (((I : LieSubalgebra R L).coe_bracket x y).symm.trans
          ((coe_zero_iff_zero _ _).mpr (by apply h.trivial))),
      fun h => ⟨fun x y => ((I : LieSubalgebra R L).coe_zero_iff_zero _).mp (h _ x y rfl)⟩⟩

variable {I N} in
/--
lemma `lie_eq_self_of_isAtom_of_ne_bot` / 引理 `lie_eq_self_of_isAtom_of_ne_bot`

English:
lemma lie_eq_self_of_isAtom_of_ne_bot
  given: (hN : IsAtom N) (h : ⁅I, N⁆ != ⊥)
  statement: ⁅I, N⁆ = N
  proof: (hN.le_iff_eq h).mp LieSubmodule.lie_le_right N I

中文:
引理 lie_eq_self_of_isAtom_of_ne_bot
  条件: (hN : IsAtom N) (h : ⁅I, N⁆ != ⊥)
  结论: ⁅I, N⁆ = N
  证明: (hN.le_iff_eq h).mp LieSubmodule.lie_le_right N I

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_le_right, hN.le_iff_eq, le_iff_eq, lie_le_right
-/
lemma lie_eq_self_of_isAtom_of_ne_bot (hN : IsAtom N) (h : ⁅I, N⁆ != ⊥) : ⁅I, N⁆ = N :=
(hN.le_iff_eq h).mp LieSubmodule.lie_le_right N I

-- TODO: introduce typeclass for perfect Lie algebras and use it here in the conclusion
/--
lemma `lie_eq_self_of_isAtom_of_nonabelian` / 引理 `lie_eq_self_of_isAtom_of_nonabelian`

English:
lemma lie_eq_self_of_isAtom_of_nonabelian
  statement: {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  proof: lie_eq_self_of_isAtom_of_ne_bot hI not_imp_not.mpr (lie_abelian_iff_lie_self_eq_bot I).mpr h

中文:
引理 lie_eq_self_of_isAtom_of_nonabelian
  结论: {R L : 类型} [CommRing R] [LieRing L] [LieAlgebra R L]
  证明: lie_eq_self_of_isAtom_of_ne_bot hI not_imp_not.mpr (lie_abelian_iff_lie_self_eq_bot I).mpr h

Depends on / 依赖: lie_abelian_iff_lie_self_eq_bot, lie_eq_self_of_isAtom_of_ne_bot, not_imp_not, not_imp_not.mpr
-/
lemma lie_eq_self_of_isAtom_of_nonabelian {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) (hI : IsAtom I) (h : ¬IsLieAbelian I) :
    ⁅I, I⁆ = I :=
lie_eq_self_of_isAtom_of_ne_bot hI not_imp_not.mpr (lie_abelian_iff_lie_self_eq_bot I).mpr h

end IdealOperations

section TrivialLieModule

set_option linter.unusedVariables false in
/-- A type synonym for an `R`-module to have a trivial Lie module structure. -/
@[nolint unusedArguments]
/--
Definition of `TrivialLieModule` / `TrivialLieModule` 的定义

English:
definition TrivialLieModule
  signature: (R L M : Type*)
  body: M

中文:
定义 TrivialLieModule
  签名: (R L M : 类型)
  定义体: M
-/
def TrivialLieModule (R L M : Type*) := M

namespace TrivialLieModule

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (TrivialLieModule R L M)
  body: inferInstanceAs (AddCommGroup M)

中文:
实例 :
  签名: AddCommGroup (TrivialLieModule R L M)
  定义体: inferInstanceAs (AddCommGroup M)

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup (TrivialLieModule R L M) := inferInstanceAs (AddCommGroup M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (TrivialLieModule R L M)
  body: inferInstanceAs (Module R M)

中文:
实例 :
  签名: Module R (TrivialLieModule R L M)
  定义体: inferInstanceAs (Module R M)

Depends on / 依赖: Module
-/
instance : Module R (TrivialLieModule R L M) := inferInstanceAs (Module R M)

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : (TrivialLieModule R L M) ≃ₗ[R] M
  body: LinearEquiv.refl R M

中文:
定义 equiv
  签名: : (TrivialLieModule R L M) ≃ₗ[R] M
  定义体: LinearEquiv.refl R M

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def equiv : (TrivialLieModule R L M) ≃ₗ[R] M := LinearEquiv.refl R M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRingModule L (TrivialLieModule R L M)
  body: 0
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp

中文:
实例 :
  签名: LieRingModule L (TrivialLieModule R L M)
  定义体: 0
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp
-/
instance : LieRingModule L (TrivialLieModule R L M) where
  bracket x m := 0
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule.IsTrivial L (TrivialLieModule R L M)
  body: rfl

中文:
实例 :
  签名: LieModule.IsTrivial L (TrivialLieModule R L M)
  定义体: rfl
-/
instance : LieModule.IsTrivial L (TrivialLieModule R L M) where
  trivial _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule R L (TrivialLieModule R L M)
  body: by simp [trivial_lie_zero]
  lie_smul := by simp [trivial_lie_zero]

中文:
实例 :
  签名: LieModule R L (TrivialLieModule R L M)
  定义体: by simp [trivial_lie_zero]
  lie_smul := by simp [trivial_lie_zero]

Depends on / 依赖: lie_smul, trivial_lie_zero
-/
instance : LieModule R L (TrivialLieModule R L M) where
  smul_lie := by simp [trivial_lie_zero]
  lie_smul := by simp [trivial_lie_zero]

end TrivialLieModule

end TrivialLieModule
