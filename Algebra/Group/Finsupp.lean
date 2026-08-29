/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finsupp.Single

/-!
# Additive monoid structure on `ι →₀ M`
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Finset

noncomputable section

variable {ι F M N O G H : Type*}

namespace Finsupp
section Zero
variable [Zero M] [Zero N] [Zero O]

/--
lemma `apply_single` / 引理 `apply_single`

English:
lemma apply_single
  given: [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) (b : ι)
  proof: apply_single' e (map_zero e) i m b

中文:
引理 apply_single
  条件: [函数状 F M N] [保零态射类 F M N] (e : F) (i : ι) (m : M) (b : ι)
  证明: apply_single' e (map_zero e) i m b

Depends on / 依赖: apply_single, map_zero
-/
lemma apply_single [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) (b : ι) :
    e (single i m b) = single i (e m) b := apply_single' e (map_zero e) i m b

/-- Composition with a fixed zero-preserving homomorphism is itself a zero-preserving homomorphism
on functions. -/
@[simps]
/--
Definition of `mapRange.zeroHom` / `mapRange.zeroHom` 的定义

English:
definition mapRange.zeroHom
  signature: (f : ZeroHom M N)
  body: Finsupp.mapRange f f.map_zero
  map_zero' := mapRange_zero

中文:
定义 mapRange.zeroHom
  签名: (f : 保零态射 M N)
  定义体: Finsupp.mapRange f f.map_zero
  map_zero' := mapRange_zero

Depends on / 依赖: Finsupp, Finsupp.mapRange, f.map_zero, mapRange, map_zero
-/
def mapRange.zeroHom (f : ZeroHom M N) : ZeroHom (ι ->₀ M) (ι ->₀ N) where
  toFun := Finsupp.mapRange f f.map_zero
  map_zero' := mapRange_zero

/--
lemma `mapRange.zeroHom_id` / 引理 `mapRange.zeroHom_id`

English:
lemma mapRange.zeroHom_id
  statement: mapRange.zeroHom (.id M) = .id (ι ->₀ M)
  proof: by ext; simp

中文:
引理 mapRange.zeroHom_id
  结论: mapRange.zeroHom (.id M) = .id (ι ->₀ M)
  证明: by ext; simp
-/
@[simp] lemma mapRange.zeroHom_id : mapRange.zeroHom (.id M) = .id (ι ->₀ M) := by ext; simp

/--
lemma `mapRange.zeroHom_comp` / 引理 `mapRange.zeroHom_comp`

English:
lemma mapRange.zeroHom_comp
  given: (f : ZeroHom N O) (f₂ : ZeroHom M N)
  proof: by
  ext; simp

中文:
引理 mapRange.zeroHom_comp
  条件: (f : 保零态射 N O) (f₂ : 保零态射 M N)
  证明: by
  ext; simp

Depends on / 依赖: f.comp, mapRange, mapRange.zeroHom, zeroHom
-/
lemma mapRange.zeroHom_comp (f : ZeroHom N O) (f₂ : ZeroHom M N) :
    mapRange.zeroHom (ι := ι) (f.comp f₂) = (mapRange.zeroHom f).comp (mapRange.zeroHom f₂) := by
  ext; simp

end Zero

section AddZeroClass
variable [AddZeroClass M] [AddZeroClass N] {f : M -> N} {g₁ g₂ : ι ->₀ M}

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (ι ->₀ M) where add
  body: zipWith (· + ·) (add_zero 0)

中文:
实例 instAdd
  签名: : 加法 (ι ->₀ M) where add
  定义体: zipWith (· + ·) (add_zero 0)

Depends on / 依赖: add_zero, zipWith
-/
instance instAdd : Add (ι ->₀ M) where add := zipWith (· + ·) (add_zero 0)

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (f g : ι ->₀ M)
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
引理 coe_add
  条件: (f g : ι ->₀ M)
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (f g : ι ->₀ M) : ⇑(f + g) = f + g := rfl

/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (g₁ g₂ : ι ->₀ M) (a : ι)
  statement: (g₁ + g₂) a = g₁ a + g₂ a
  proof: rfl

中文:
引理 add_apply
  条件: (g₁ g₂ : ι ->₀ M) (a : ι)
  结论: (g₁ + g₂) a = g₁ a + g₂ a
  证明: rfl
-/
lemma add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

/--
lemma `support_add` / 引理 `support_add`

English:
lemma support_add
  given: [DecidableEq ι]
  statement: (g₁ + g₂).support subseteq g₁.support union g₂.support
  proof: support_zipWith

中文:
引理 support_add
  条件: [DecidableEq ι]
  结论: (g₁ + g₂).support subseteq g₁.support union g₂.support
  证明: support_zipWith

Depends on / 依赖: support_zipWith
-/
lemma support_add [DecidableEq ι] : (g₁ + g₂).support subseteq g₁.support union g₂.support := support_zipWith

/--
lemma `support_add_eq` / 引理 `support_add_eq`

English:
lemma support_add_eq
  given: [DecidableEq ι] (h : Disjoint g₁.support g₂.support)
  proof: le_antisymm support_zipWith fun a ha => by
    cases (Finset.mem_union_of_disjoint h).mp ha <;> simp_all

中文:
引理 support_add_eq
  条件: [DecidableEq ι] (h : Disjoint g₁.support g₂.support)
  证明: le_antisymm support_zipWith fun a ha => by
    cases (Finset.mem_union_of_disjoint h).mp ha <;> simp_all

Depends on / 依赖: Finset, Finset.mem_union_of_disjoint, le_antisymm, mem_union_of_disjoint, support_zipWith
-/
lemma support_add_eq [DecidableEq ι] (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support union g₂.support :=
  le_antisymm support_zipWith fun a ha => by
    cases (Finset.mem_union_of_disjoint h).mp ha <;> simp_all

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: : AddZeroClass (ι ->₀ M)
  body: fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

中文:
实例 instAddZeroClass
  签名: : 加法零类 (ι ->₀ M)
  定义体: fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addZeroClass, addZeroClass, coe_add, coe_injective, coe_zero, fast_instance
-/
instance instAddZeroClass : AddZeroClass (ι ->₀ M) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

/--
Instance `instIsLeftCancelAdd` / 实例 `instIsLeftCancelAdd`

English:
instance instIsLeftCancelAdd
  signature: [IsLeftCancelAdd M]
  body: ext fun x => add_left_cancel DFunLike.congr_fun h x

中文:
实例 instIsLeftCancelAdd
  签名: [是左消去加法 M]
  定义体: ext fun x => add_left_cancel DFunLike.congr_fun h x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, add_left_cancel, congr_fun
-/
instance instIsLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd (ι ->₀ M) where
add_left_cancel _ _ _ h := ext fun x => add_left_cancel DFunLike.congr_fun h x

/--
Definition of `addEquivFunOnFinite` / `addEquivFunOnFinite` 的定义

English:
definition addEquivFunOnFinite
  signature: {ι : Type*} [Finite ι]
  body: Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

中文:
定义 addEquivFunOnFinite
  签名: {ι : 类型} [有限 ι]
  定义体: Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite, equivFunOnFinite
-/
noncomputable def addEquivFunOnFinite {ι : Type*} [Finite ι] :
    (ι ->₀ M) ≃+ (ι -> M) where
  __ := Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

/-- If `M` is the trivial monoid, then the monoid of finitely supported functions `ι →₀ M` is
is isomorphic to `M`. -/
@[simps! apply symm_apply]
/--
Definition of `uniqueAddEquiv` / `uniqueAddEquiv` 的定义

English:
definition uniqueAddEquiv
  signature: (i : ι) [Subsingleton ι]
  body: uniqueEquiv i
  map_add' _ _ := rfl

中文:
定义 uniqueAddEquiv
  签名: (i : ι) [子单例 ι]
  定义体: uniqueEquiv i
  map_add' _ _ := rfl

Depends on / 依赖: uniqueEquiv
-/
noncomputable def uniqueAddEquiv (i : ι) [Subsingleton ι] : (ι ->₀ M) ≃+ M where
  toEquiv := uniqueEquiv i
  map_add' _ _ := rfl

-- We want this lemma to fire before `uniqueAddEquiv_symm_apply`.
/--
lemma `uniqueAddEquiv_symm_apply_apply` / 引理 `uniqueAddEquiv_symm_apply_apply`

English:
lemma uniqueAddEquiv_symm_apply_apply
  given: (i : ι) [Subsingleton ι] (m : M) (j : ι)
  proof: by simp [Subsingleton.elim j i]

中文:
引理 uniqueAddEquiv_symm_apply_apply
  条件: (i : ι) [子单例 ι] (m : M) (j : ι)
  证明: by simp [Subsingleton.elim j i]
-/
@[simp↓ high] lemma uniqueAddEquiv_symm_apply_apply (i : ι) [Subsingleton ι] (m : M) (j : ι) :
    (uniqueAddEquiv i).symm m j = m := by simp [Subsingleton.elim j i]

/-- If `M` is the trivial monoid, then the monoid of finitely supported functions `ι →₀ M` is
is isomorphic to `M`. -/
@[simps!, deprecated uniqueAddEquiv (since := "2026-05-06")]
/--
Definition of `_root_.AddEquiv.finsuppUnique` / `_root_.AddEquiv.finsuppUnique` 的定义

English:
definition _root_.AddEquiv.finsuppUnique
  signature: {ι : Type*} [Unique ι]
  body: .finsuppUnique
  map_add' _ _ := rfl

中文:
定义 _root_.加法等价.finsuppUnique
  签名: {ι : 类型} [唯一 ι]
  定义体: .finsuppUnique
  map_add' _ _ := rfl

Depends on / 依赖: finsuppUnique
-/
noncomputable def _root_.AddEquiv.finsuppUnique {ι : Type*} [Unique ι] : (ι ->₀ M) ≃+ M where
  toEquiv := .finsuppUnique
  map_add' _ _ := rfl

/--
Instance `instIsRightCancelAdd` / 实例 `instIsRightCancelAdd`

English:
instance instIsRightCancelAdd
  signature: [IsRightCancelAdd M]
  body: ext fun x => add_right_cancel DFunLike.congr_fun h x

中文:
实例 instIsRightCancelAdd
  签名: [是右消去加法 M]
  定义体: ext fun x => add_right_cancel DFunLike.congr_fun h x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, add_right_cancel, congr_fun
-/
instance instIsRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd (ι ->₀ M) where
add_right_cancel _ _ _ h := ext fun x => add_right_cancel DFunLike.congr_fun h x

/--
Instance `instIsCancelAdd` / 实例 `instIsCancelAdd`

English:
instance instIsCancelAdd
  signature: [IsCancelAdd M]

中文:
实例 instIsCancelAdd
  签名: [是消去加法 M]
-/
instance instIsCancelAdd [IsCancelAdd M] : IsCancelAdd (ι ->₀ M) where

/-- Evaluation of a function `f : ι →₀ M` at a point as an additive monoid homomorphism.

See `Finsupp.lapply` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps apply]
/--
Definition of `applyAddHom` / `applyAddHom` 的定义

English:
definition applyAddHom
  signature: (a : ι)
  body: g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _

中文:
定义 applyAddHom
  签名: (a : ι)
  定义体: g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _
-/
def applyAddHom (a : ι) : (ι ->₀ M) ->+ M where
  toFun g := g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _

/-- Coercion from a `Finsupp` to a function type is an `AddMonoidHom`. -/
@[simps]
/--
Definition of `coeFnAddHom` / `coeFnAddHom` 的定义

English:
definition coeFnAddHom
  signature: : (ι ->₀ M) ->+ ι -> M where
  body: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

中文:
定义 coeFnAddHom
  签名: : (ι ->₀ M) ->+ ι -> M where
  定义体: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
-/
noncomputable def coeFnAddHom : (ι ->₀ M) ->+ ι -> M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

/--
lemma `mapRange_add` / 引理 `mapRange_add`

English:
lemma mapRange_add
  given: {hf : f 0 = 0} (hf' : forall x y, f (x + y) = f x + f y) (v₁ v₂ : ι ->₀ M)
  proof: ext fun _ => by simp only [hf', add_apply, mapRange_apply]

中文:
引理 mapRange_add
  条件: {hf : f 0 = 0} (hf' : 对任意 x y, f (x + y) = f x + f y) (v₁ v₂ : ι ->₀ M)
  证明: ext fun _ => by simp only [hf', add_apply, mapRange_apply]

Depends on / 依赖: add_apply, mapRange_apply
-/
lemma mapRange_add {hf : f 0 = 0} (hf' : forall x y, f (x + y) = f x + f y) (v₁ v₂ : ι ->₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, mapRange_apply]

/--
lemma `mapRange_add'` / 引理 `mapRange_add'`

English:
lemma mapRange_add'
  given: [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι ->₀ M)
  proof: mapRange_add (map_add f) g₁ g₂

中文:
引理 mapRange_add'
  条件: [函数状 F M N] [加法幺半群态射类 F M N] {f : F} (g₁ g₂ : ι ->₀ M)
  证明: mapRange_add (map_add f) g₁ g₂

Depends on / 依赖: mapRange_add, map_add
-/
lemma mapRange_add' [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι ->₀ M) :
    mapRange f (map_zero f) (g₁ + g₂) = mapRange f (map_zero f) g₁ + mapRange f (map_zero f) g₂ :=
  mapRange_add (map_add f) g₁ g₂

/-- Bundle `Finsupp.embDomain f` as an additive map from `ι →₀ M` to `F →₀ M`. -/
@[simps]
/--
Definition of `embDomain.addMonoidHom` / `embDomain.addMonoidHom` 的定义

English:
definition embDomain.addMonoidHom
  signature: (f : ι ↪ F)
  body: embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b in Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [coe_add, Pi.add_apply, embDomain_of_notMem_range _ _ _ h, add_zero]

@[simp]

中文:
定义 embDomain.addMonoidHom
  签名: (f : ι ↪ F)
  定义体: embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b in Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [coe_add, Pi.add_apply, embDomain_of_notMem_range _ _ _ h, add_zero]

@[simp]

Depends on / 依赖: congr_fun, embDomain, eq_id, h.eq_id
-/
def embDomain.addMonoidHom (f : ι ↪ F) : (ι ->₀ M) ->+ F ->₀ M where
  toFun v := embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b in Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [coe_add, Pi.add_apply, embDomain_of_notMem_range _ _ _ h, add_zero]

@[simp]
/--
lemma `embDomain_add` / 引理 `embDomain_add`

English:
lemma embDomain_add
  given: (f : ι ↪ F) (v w : ι ->₀ M)
  proof: (embDomain.addMonoidHom f).map_add v w

@[simp]

中文:
引理 embDomain_add
  条件: (f : ι ↪ F) (v w : ι ->₀ M)
  证明: (embDomain.addMonoidHom f).map_add v w

@[simp]

Depends on / 依赖: addMonoidHom, embDomain, embDomain.addMonoidHom, map_add
-/
lemma embDomain_add (f : ι ↪ F) (v w : ι ->₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w := (embDomain.addMonoidHom f).map_add v w

@[simp]
/--
lemma `single_add` / 引理 `single_add`

English:
lemma single_add
  given: (a : ι) (b₁ b₂ : M)
  statement: single a (b₁ + b₂) = single a b₁ + single a b₂
  proof: (zipWith_single_single _ _ _ _ _).symm

中文:
引理 single_add
  条件: (a : ι) (b₁ b₂ : M)
  结论: single a (b₁ + b₂) = single a b₁ + single a b₂
  证明: (zipWith_single_single _ _ _ _ _).symm

Depends on / 依赖: zipWith_single_single
-/
lemma single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm

/--
lemma `single_add_apply` / 引理 `single_add_apply`

English:
lemma single_add_apply
  given: (a : ι) (m₁ m₂ : M) (b : ι)
  proof: by simp

中文:
引理 single_add_apply
  条件: (a : ι) (m₁ m₂ : M) (b : ι)
  证明: by simp
-/
lemma single_add_apply (a : ι) (m₁ m₂ : M) (b : ι) :
    single a (m₁ + m₂) b = single a m₁ b + single a m₂ b := by simp

/--
lemma `support_single_add` / 引理 `support_single_add`

English:
lemma support_single_add
  given: {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb : b != 0)
  proof: by
  classical
  have H := support_single a hb
  rw [support_add_eq]; rw [H]; rw [cons_eq_insert]; rw [insert_eq]
  rwa [H, disjoint_singleton_left]

中文:
引理 support_single_add
  条件: {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb : b != 0)
  证明: by
  classical
  have H := support_single a hb
  rw [support_add_eq]; rw [H]; rw [cons_eq_insert]; rw [insert_eq]
  rwa [H, disjoint_singleton_left]

Depends on / 依赖: classical, cons_eq_insert, disjoint_singleton_left, insert_eq, support_add_eq, support_single
-/
lemma support_single_add {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb : b != 0) :
    support (single a b + f) = cons a f.support ha := by
  classical
  have H := support_single a hb
  rw [support_add_eq]; rw [H]; rw [cons_eq_insert]; rw [insert_eq]
  rwa [H, disjoint_singleton_left]

/--
lemma `support_add_single` / 引理 `support_add_single`

English:
lemma support_add_single
  given: {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb : b != 0)
  proof: by
  classical
  have H := support_single a hb
  rw [support_add_eq]; rw [H]; rw [union_comm]; rw [cons_eq_insert]; rw [insert_eq]
  rwa [H, disjoint_singleton_right]

中文:
引理 support_add_single
  条件: {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb : b != 0)
  证明: by
  classical
  have H := support_single a hb
  rw [support_add_eq]; rw [H]; rw [union_comm]; rw [cons_eq_insert]; rw [insert_eq]
  rwa [H, disjoint_singleton_right]

Depends on / 依赖: classical, cons_eq_insert, disjoint_singleton_right, insert_eq, support_add_eq, support_single, union_comm
-/
lemma support_add_single {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb : b != 0) :
    support (f + single a b) = cons a f.support ha := by
  classical
  have H := support_single a hb
  rw [support_add_eq]; rw [H]; rw [union_comm]; rw [cons_eq_insert]; rw [insert_eq]
  rwa [H, disjoint_singleton_right]

/--
lemma `support_single_add_single` / 引理 `support_single_add_single`

English:
lemma support_single_add_single
  statement: [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
  proof: by
  rw [support_add_eq]; rw [support_single _ hg₁]; rw [support_single _ hg₂]
  · simp
  · simp [support_single, *]

中文:
引理 support_single_add_single
  结论: [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
  证明: by
  rw [support_add_eq]; rw [support_single _ hg₁]; rw [support_single _ hg₂]
  · simp
  · simp [support_single, *]

Depends on / 依赖: support_add_eq, support_single
-/
lemma support_single_add_single [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
    (H : f₁ != f₂) (hg₁ : g₁ != 0) (hg₂ : g₂ != 0) :
    (single f₁ g₁ + single f₂ g₂).support = {f₁, f₂} := by
  rw [support_add_eq]; rw [support_single _ hg₁]; rw [support_single _ hg₂]
  · simp
  · simp [support_single, *]

/--
lemma `support_single_add_single_subset` / 引理 `support_single_add_single_subset`

English:
lemma support_single_add_single_subset
  given: [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
  proof: by
refine subset_trans Finsupp.support_add union_subset_iff.mpr ⟨?_, ?_⟩ <;>
  exact subset_trans Finsupp.support_single_subset (by simp)

中文:
引理 support_single_add_single_subset
  条件: [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
  证明: by
refine subset_trans Finsupp.support_add union_subset_iff.mpr ⟨?_, ?_⟩ <;>
  exact subset_trans Finsupp.support_single_subset (by simp)

Depends on / 依赖: Finsupp, Finsupp.support_add, Finsupp.support_single_subset, subset_trans, support_add, support_single_subset, union_subset_iff, union_subset_iff.mpr
-/
lemma support_single_add_single_subset [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M} :
    (single f₁ g₁ + single f₂ g₂).support subseteq {f₁, f₂} := by
refine subset_trans Finsupp.support_add union_subset_iff.mpr ⟨?_, ?_⟩ <;>
  exact subset_trans Finsupp.support_single_subset (by simp)

set_option backward.isDefEq.respectTransparency false in
@[deprecated uniqueAddEquiv_symm_apply (since := "2026-05-06")]
/--
lemma `_root_.AddEquiv.finsuppUnique_symm` / 引理 `_root_.AddEquiv.finsuppUnique_symm`

English:
lemma _root_.AddEquiv.finsuppUnique_symm
  given: {M : Type*} [AddZeroClass M] (d : M)
  proof: by ext; simp [AddEquiv.finsuppUnique]

中文:
引理 _root_.加法等价.finsuppUnique_symm
  条件: {M : 类型} [加法零类 M] (d : M)
  证明: by ext; simp [AddEquiv.finsuppUnique]

Depends on / 依赖: AddEquiv, AddEquiv.finsuppUnique, finsuppUnique
-/
lemma _root_.AddEquiv.finsuppUnique_symm {M : Type*} [AddZeroClass M] (d : M) :
    AddEquiv.finsuppUnique.symm d = single () d := by ext; simp [AddEquiv.finsuppUnique]

/--
theorem `addCommute_iff_inter` / 定理 `addCommute_iff_inter`

English:
theorem addCommute_iff_inter
  given: [DecidableEq ι] {f g : ι ->₀ M}
  proof: fun x _ => Finsupp.ext_iff.1 h x
  mpr h := by
    ext x
    by_cases hf : x in f.support
    · by_cases hg : x in g.support
      · exact h _ (mem_inter_of_mem hf hg)
      · simp_all
    · simp_all

中文:
定理 addCommute_iff_inter
  条件: [DecidableEq ι] {f g : ι ->₀ M}
  证明: fun x _ => Finsupp.ext_iff.1 h x
  mpr h := by
    ext x
    by_cases hf : x in f.support
    · by_cases hg : x in g.support
      · exact h _ (mem_inter_of_mem hf hg)
      · simp_all
    · simp_all

Depends on / 依赖: Finsupp, Finsupp.ext_iff, ext_iff
-/
theorem addCommute_iff_inter [DecidableEq ι] {f g : ι ->₀ M} :
    AddCommute f g ↔ forall x in f.support inter g.support, AddCommute (f x) (g x) where
  mp h := fun x _ => Finsupp.ext_iff.1 h x
  mpr h := by
    ext x
    by_cases hf : x in f.support
    · by_cases hg : x in g.support
      · exact h _ (mem_inter_of_mem hf hg)
      · simp_all
    · simp_all

/--
theorem `addCommute_of_disjoint` / 定理 `addCommute_of_disjoint`

English:
theorem addCommute_of_disjoint
  given: {f g : ι ->₀ M} (h : Disjoint f.support g.support)
  proof: by
  classical simp_all [addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

中文:
定理 addCommute_of_disjoint
  条件: {f g : ι ->₀ M} (h : Disjoint f.support g.support)
  证明: by
  classical simp_all [addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

Depends on / 依赖: Finset, Finset.disjoint_iff_inter_eq_empty, addCommute_iff_inter, classical, disjoint_iff_inter_eq_empty, map_mul, map_one
-/
theorem addCommute_of_disjoint {f g : ι ->₀ M} (h : Disjoint f.support g.support) :
    AddCommute f g := by
  classical simp_all [addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

/-- `Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps]
/--
Definition of `singleAddHom` / `singleAddHom` 的定义

English:
definition singleAddHom
  signature: (a : ι)
  body: single a
  map_zero' := single_zero a
  map_add' := single_add a

中文:
定义 singleAddHom
  签名: (a : ι)
  定义体: single a
  map_zero' := single_zero a
  map_add' := single_add a

Depends on / 依赖: single
-/
def singleAddHom (a : ι) : M ->+ ι ->₀ M where
  toFun := single a
  map_zero' := single_zero a
  map_add' := single_add a

/--
lemma `update_eq_single_add_erase` / 引理 `update_eq_single_add_erase`

English:
lemma update_eq_single_add_erase
  given: (f : ι ->₀ M) (a : ι) (b : M)
  proof: by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

中文:
引理 update_eq_single_add_erase
  条件: (f : ι ->₀ M) (a : ι) (b : M)
  证明: by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

Depends on / 依赖: classical, eq_or_ne, erase_ne
-/
lemma update_eq_single_add_erase (f : ι ->₀ M) (a : ι) (b : M) :
    f.update a b = single a b + f.erase a := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

/--
lemma `update_eq_erase_add_single` / 引理 `update_eq_erase_add_single`

English:
lemma update_eq_erase_add_single
  given: (f : ι ->₀ M) (a : ι) (b : M)
  proof: by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

中文:
引理 update_eq_erase_add_single
  条件: (f : ι ->₀ M) (a : ι) (b : M)
  证明: by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

Depends on / 依赖: classical, eq_or_ne, erase_ne
-/
lemma update_eq_erase_add_single (f : ι ->₀ M) (a : ι) (b : M) :
    f.update a b = f.erase a + single a b := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

/--
lemma `update_eq_single_add` / 引理 `update_eq_single_add`

English:
lemma update_eq_single_add
  given: {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M)
  proof: by
  rw [update_eq_single_add_erase]; rw [erase_of_notMem_support (by simpa)]

中文:
引理 update_eq_single_add
  条件: {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M)
  证明: by
  rw [update_eq_single_add_erase]; rw [erase_of_notMem_support (by simpa)]

Depends on / 依赖: erase_of_notMem_support, update_eq_single_add_erase
-/
lemma update_eq_single_add {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = single a b + f := by
  rw [update_eq_single_add_erase]; rw [erase_of_notMem_support (by simpa)]

/--
lemma `update_eq_add_single` / 引理 `update_eq_add_single`

English:
lemma update_eq_add_single
  given: {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M)
  proof: by
  rw [update_eq_erase_add_single]; rw [erase_of_notMem_support (by simpa)]

中文:
引理 update_eq_add_single
  条件: {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M)
  证明: by
  rw [update_eq_erase_add_single]; rw [erase_of_notMem_support (by simpa)]

Depends on / 依赖: erase_of_notMem_support, update_eq_erase_add_single
-/
lemma update_eq_add_single {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = f + single a b := by
  rw [update_eq_erase_add_single]; rw [erase_of_notMem_support (by simpa)]

/--
lemma `single_add_erase` / 引理 `single_add_erase`

English:
lemma single_add_erase
  given: (a : ι) (f : ι ->₀ M)
  statement: single a (f a) + f.erase a = f
  proof: by
  rw [← update_eq_single_add_erase]; rw [update_self]

中文:
引理 single_add_erase
  条件: (a : ι) (f : ι ->₀ M)
  结论: single a (f a) + f.erase a = f
  证明: by
  rw [← update_eq_single_add_erase]; rw [update_self]

Depends on / 依赖: update_eq_single_add_erase, update_self
-/
lemma single_add_erase (a : ι) (f : ι ->₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase]; rw [update_self]

/--
lemma `erase_add_single` / 引理 `erase_add_single`

English:
lemma erase_add_single
  given: (a : ι) (f : ι ->₀ M)
  statement: f.erase a + single a (f a) = f
  proof: by
  rw [← update_eq_erase_add_single]; rw [update_self]

@[simp]

中文:
引理 erase_add_single
  条件: (a : ι) (f : ι ->₀ M)
  结论: f.erase a + single a (f a) = f
  证明: by
  rw [← update_eq_erase_add_single]; rw [update_self]

@[simp]

Depends on / 依赖: update_eq_erase_add_single, update_self
-/
lemma erase_add_single (a : ι) (f : ι ->₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single]; rw [update_self]

@[simp]
/--
lemma `erase_add` / 引理 `erase_add`

English:
lemma erase_add
  given: (a : ι) (f f' : ι ->₀ M)
  statement: erase a (f + f') = erase a f + erase a f'
  proof: by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply]; rw [erase_ne hs]; rw [erase_ne hs]; rw [erase_ne hs]; rw [add_apply]

中文:
引理 erase_add
  条件: (a : ι) (f f' : ι ->₀ M)
  结论: erase a (f + f') = erase a f + erase a f'
  证明: by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply]; rw [erase_ne hs]; rw [erase_ne hs]; rw [erase_ne hs]; rw [add_apply]

Depends on / 依赖: add_apply, add_zero, erase_ne, erase_same
-/
lemma erase_add (a : ι) (f f' : ι ->₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply]; rw [erase_ne hs]; rw [erase_ne hs]; rw [erase_ne hs]; rw [add_apply]

/-- `Finsupp.erase` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `eraseAddHom` / `eraseAddHom` 的定义

English:
definition eraseAddHom
  signature: (a : ι)
  body: erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_elim]

中文:
定义 eraseAddHom
  签名: (a : ι)
  定义体: erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_elim]
-/
def eraseAddHom (a : ι) : (ι ->₀ M) ->+ ι ->₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_elim]
/--
lemma `induction` / 引理 `induction`

English:
lemma induction
  statement: {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive 0)
  proof: suffices forall (s) (f : ι ->₀ M), f.support = s -> motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply single_add
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase]; rw [hf]; rw [Finset.erase_cons]

@[elab_as_elim]

中文:
引理 induction
  结论: {motive : (ι ->₀ M) -> 命题} (f : ι ->₀ M) (zero : motive 0)
  证明: suffices forall (s) (f : ι ->₀ M), f.support = s -> motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply single_add
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase]; rw [hf]; rw [Finset.erase_cons]

@[elab_as_elim]
-/
protected lemma induction {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive 0)
    (single_add : forall (a b) (f : ι ->₀ M),
      a ∉ f.support -> b != 0 -> motive f -> motive (single a b + f)) : motive f :=
  suffices forall (s) (f : ι ->₀ M), f.support = s -> motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply single_add
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase]; rw [hf]; rw [Finset.erase_cons]

@[elab_as_elim]
/--
lemma `induction₂` / 引理 `induction₂`

English:
lemma induction₂
  statement: {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive 0)
  proof: by
  refine f.induction zero ?_
  convert! add_single using 7
  apply (addCommute_of_disjoint _).eq
  simp_all

@[elab_as_elim]

中文:
引理 induction₂
  结论: {motive : (ι ->₀ M) -> 命题} (f : ι ->₀ M) (zero : motive 0)
  证明: by
  refine f.induction zero ?_
  convert! add_single using 7
  apply (addCommute_of_disjoint _).eq
  simp_all

@[elab_as_elim]

Depends on / 依赖: addCommute_of_disjoint, add_single, convert, f.induction
-/
lemma induction₂ {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive 0)
    (add_single : forall (a b) (f : ι ->₀ M),
      a ∉ f.support -> b != 0 -> motive f -> motive (f + single a b)) : motive f := by
  refine f.induction zero ?_
  convert! add_single using 7
  apply (addCommute_of_disjoint _).eq
  simp_all

@[elab_as_elim]
/--
lemma `induction_linear` / 引理 `induction_linear`

English:
lemma induction_linear
  statement: {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive 0)
  proof: induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

中文:
引理 induction_linear
  结论: {motive : (ι ->₀ M) -> 命题} (f : ι ->₀ M) (zero : motive 0)
  证明: induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

Depends on / 依赖: single
-/
lemma induction_linear {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive 0)
    (add : forall f g : ι ->₀ M, motive f -> motive g -> motive (f + g))
    (single : forall a b, motive (single a b)) : motive f :=
  induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

section LinearOrder

variable [LinearOrder ι] {motive : (ι ->₀ M) -> Prop}

/--
lemma `induction_on_max` / 引理 `induction_on_max`

English:
lemma induction_on_max
  statement: (f : ι ->₀ M) (zero : motive 0)
  proof: by
  suffices forall (s) (f : ι ->₀ M), f.support = s -> motive f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase]; rw [hs]; rw [erase_insert (fun ha => (hm a ha).false)]
    rw [← single_add_erase a f]
    refine single_add _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff]; rw [hs]
    exact mem_insert_self a s

中文:
引理 induction_on_max
  结论: (f : ι ->₀ M) (zero : motive 0)
  证明: by
  suffices forall (s) (f : ι ->₀ M), f.support = s -> motive f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase]; rw [hs]; rw [erase_insert (fun ha => (hm a ha).false)]
    rw [← single_add_erase a f]
    refine single_add _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff]; rw [hs]
    exact mem_insert_self a s

Depends on / 依赖: erase_insert, f.support, induction_on_max, mem_insert_self, mem_support_iff, motive, s.induction_on_max, single_add, single_add_erase, support, support_eq_empty, support_erase
-/
lemma induction_on_max (f : ι ->₀ M) (zero : motive 0)
    (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b != 0 ->
      motive f -> motive (single a b + f)) : motive f := by
  suffices forall (s) (f : ι ->₀ M), f.support = s -> motive f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase]; rw [hs]; rw [erase_insert (fun ha => (hm a ha).false)]
    rw [← single_add_erase a f]
    refine single_add _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff]; rw [hs]
    exact mem_insert_self a s

/--
lemma `induction_on_min` / 引理 `induction_on_min`

English:
lemma induction_on_min
  statement: (f : ι ->₀ M) (zero : motive 0)
  proof: induction_on_max (ι := ιᵒᵈ) f zero single_add

中文:
引理 induction_on_min
  结论: (f : ι ->₀ M) (zero : motive 0)
  证明: induction_on_max (ι := ιᵒᵈ) f zero single_add

Depends on / 依赖: induction_on_max, single_add
-/
lemma induction_on_min (f : ι ->₀ M) (zero : motive 0)
    (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, a < c) -> b != 0 ->
      motive f -> motive (single a b + f)) : motive f :=
  induction_on_max (ι := ιᵒᵈ) f zero single_add

/--
lemma `induction_on_max₂` / 引理 `induction_on_max₂`

English:
lemma induction_on_max₂
  statement: (f : ι ->₀ M) (zero : motive 0)
  proof: by
  refine f.induction_on_max zero ?_
  convert! add_single using 7 with _ _ _ H
  have := fun c hc => (H c hc).ne
  apply (addCommute_of_disjoint _).eq
  simp_all [not_imp_not]

中文:
引理 induction_on_max₂
  结论: (f : ι ->₀ M) (zero : motive 0)
  证明: by
  refine f.induction_on_max zero ?_
  convert! add_single using 7 with _ _ _ H
  have := fun c hc => (H c hc).ne
  apply (addCommute_of_disjoint _).eq
  simp_all [not_imp_not]

Depends on / 依赖: addCommute_of_disjoint, add_single, convert, f.induction_on_max, induction_on_max, not_imp_not
-/
lemma induction_on_max₂ (f : ι ->₀ M) (zero : motive 0)
    (add_single : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b != 0 ->
      motive f -> motive (f + single a b)) : motive f := by
  refine f.induction_on_max zero ?_
  convert! add_single using 7 with _ _ _ H
  have := fun c hc => (H c hc).ne
  apply (addCommute_of_disjoint _).eq
  simp_all [not_imp_not]

/--
lemma `induction_on_min₂` / 引理 `induction_on_min₂`

English:
lemma induction_on_min₂
  statement: (f : ι ->₀ M) (zero : motive 0)
  proof: induction_on_max₂ (ι := ιᵒᵈ) f zero add_single

中文:
引理 induction_on_min₂
  结论: (f : ι ->₀ M) (zero : motive 0)
  证明: induction_on_max₂ (ι := ιᵒᵈ) f zero add_single

Depends on / 依赖: add_single
-/
lemma induction_on_min₂ (f : ι ->₀ M) (zero : motive 0)
    (add_single : forall a b (f : ι ->₀ M), (forall c in f.support, a < c) -> b != 0 ->
      motive f -> motive (f + single a b)) : motive f :=
  induction_on_max₂ (ι := ιᵒᵈ) f zero add_single

end LinearOrder

end AddZeroClass

section AddMonoid
variable [AddMonoid M]

/--
Instance `instNatSMul` / 实例 `instNatSMul`

English:
instance instNatSMul
  signature: : SMul Nat (ι ->₀ M) where smul n v
  body: v.mapRange (n • ·) (nsmul_zero _)

中文:
实例 inst自然数SMul
  签名: : 标量乘法 自然数 (ι ->₀ M) where smul n v
  定义体: v.mapRange (n • ·) (nsmul_zero _)

Depends on / 依赖: mapRange, nsmul_zero, v.mapRange
-/
instance instNatSMul : SMul Nat (ι ->₀ M) where smul n v := v.mapRange (n • ·) (nsmul_zero _)

/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (n : Nat) (f : ι ->₀ M)
  statement: ⇑(n • f) = n • ⇑f
  proof: rfl

中文:
引理 coe_nsmul
  条件: (n : 自然数) (f : ι ->₀ M)
  结论: ⇑(n • f) = n • ⇑f
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nsmul (n : Nat) (f : ι ->₀ M) : ⇑(n • f) = n • ⇑f := rfl

/--
lemma `nsmul_apply` / 引理 `nsmul_apply`

English:
lemma nsmul_apply
  given: (n : Nat) (f : ι ->₀ M) (x : ι)
  statement: (n • f) x = n • f x
  proof: rfl

中文:
引理 nsmul_apply
  条件: (n : 自然数) (f : ι ->₀ M) (x : ι)
  结论: (n • f) x = n • f x
  证明: rfl
-/
lemma nsmul_apply (n : Nat) (f : ι ->₀ M) (x : ι) : (n • f) x = n • f x := rfl

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid (ι ->₀ M)
  body: fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 instAddMonoid
  签名: : 加法幺半群 (ι ->₀ M)
  定义体: fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addMonoid, addMonoid, coe_add, coe_injective, coe_zero, fast_instance
-/
instance instAddMonoid : AddMonoid (ι ->₀ M) :=
  fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

/--
Instance `instIsAddTorsionFree` / 实例 `instIsAddTorsionFree`

English:
instance instIsAddTorsionFree
  signature: [IsAddTorsionFree M]
  body: DFunLike.coe_injective.isAddTorsionFree coeFnAddHom

中文:
实例 instIsAddTorsionFree
  签名: [是加法无挠 M]
  定义体: DFunLike.coe_injective.isAddTorsionFree coeFnAddHom

Depends on / 依赖: DFunLike, DFunLike.coe_injective.isAddTorsionFree, coeFnAddHom, coe_injective, isAddTorsionFree
-/
instance instIsAddTorsionFree [IsAddTorsionFree M] : IsAddTorsionFree (ι ->₀ M) :=
  DFunLike.coe_injective.isAddTorsionFree coeFnAddHom

end AddMonoid

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (ι ->₀ M)
  body: fast_instance% DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (ι ->₀ M)
  定义体: fast_instance% DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.addCommMonoid, addCommMonoid, coe_add, coe_injective, coe_zero, fast_instance
-/
instance instAddCommMonoid : AddCommMonoid (ι ->₀ M) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)

/--
lemma `single_add_single_eq_single_add_single` / 引理 `single_add_single_eq_single_add_single`

English:
lemma single_add_single_eq_single_add_single
  given: {k l m n : ι} {u v : M} (hu : u != 0) (hv : v != 0)
  proof: by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

中文:
引理 single_add_single_eq_single_add_single
  条件: {k l m n : ι} {u v : M} (hu : u != 0) (hv : v != 0)
  证明: by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Pi.single_add_single_eq_single_add_single, classical, coe_add, ext_iff, funext_iff, simp_rw, single_add_single_eq_single_add_single, single_eq_pi_single
-/
lemma single_add_single_eq_single_add_single {k l m n : ι} {u v : M} (hu : u != 0) (hv : v != 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

/-- Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
/--
Definition of `mapRange.addMonoidHom` / `mapRange.addMonoidHom` 的定义

English:
definition mapRange.addMonoidHom
  signature: (f : M ->+ N)
  body: mapRange f f.map_zero
  map_zero' := mapRange_zero
  map_add' := mapRange_add f.map_add

@[simp]

中文:
定义 mapRange.addMonoidHom
  签名: (f : M ->+ N)
  定义体: mapRange f f.map_zero
  map_zero' := mapRange_zero
  map_add' := mapRange_add f.map_add

@[simp]

Depends on / 依赖: f.map_zero, mapRange, map_zero
-/
def mapRange.addMonoidHom (f : M ->+ N) : (ι ->₀ M) ->+ ι ->₀ N where
  toFun := mapRange f f.map_zero
  map_zero' := mapRange_zero
  map_add' := mapRange_add f.map_add

@[simp]
/--
lemma `mapRange.addMonoidHom_id` / 引理 `mapRange.addMonoidHom_id`

English:
lemma mapRange.addMonoidHom_id
  proof: AddMonoidHom.ext mapRange_id

中文:
引理 mapRange.addMonoidHom_id
  证明: AddMonoidHom.ext mapRange_id

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, mapRange_id
-/
lemma mapRange.addMonoidHom_id :
    mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (ι ->₀ M) :=
  AddMonoidHom.ext mapRange_id

/--
lemma `mapRange.addMonoidHom_comp` / 引理 `mapRange.addMonoidHom_comp`

English:
lemma mapRange.addMonoidHom_comp
  given: (f : N ->+ O) (g : M ->+ N)
  proof: by ext; simp

@[simp]

中文:
引理 mapRange.addMonoidHom_comp
  条件: (f : N ->+ O) (g : M ->+ N)
  证明: by ext; simp

@[simp]

Depends on / 依赖: f.comp
-/
lemma mapRange.addMonoidHom_comp (f : N ->+ O) (g : M ->+ N) :
    mapRange.addMonoidHom (ι := ι) (f.comp g) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom g) := by ext; simp

@[simp]
/--
lemma `mapRange.addMonoidHom_toZeroHom` / 引理 `mapRange.addMonoidHom_toZeroHom`

English:
lemma mapRange.addMonoidHom_toZeroHom
  given: (f : M ->+ N)
  proof: rfl

中文:
引理 mapRange.addMonoidHom_toZeroHom
  条件: (f : M ->+ N)
  证明: rfl

Depends on / 依赖: f.toZeroHom, toZeroHom
-/
lemma mapRange.addMonoidHom_toZeroHom (f : M ->+ N) :
    (mapRange.addMonoidHom f).toZeroHom = mapRange.zeroHom (ι := ι) f.toZeroHom := rfl

/-- `Finsupp.mapRange.AddMonoidHom` as an equiv. -/
@[simps! apply]
/--
Definition of `mapRange.addEquiv` / `mapRange.addEquiv` 的定义

English:
definition mapRange.addEquiv
  signature: (em' : M ≃+ N)
  body: mapRange.equiv em' em'.map_zero
  __ := mapRange.addMonoidHom em'.toAddMonoidHom

@[simp]

中文:
定义 mapRange.addEquiv
  签名: (em' : M ≃+ N)
  定义体: mapRange.equiv em' em'.map_zero
  __ := mapRange.addMonoidHom em'.toAddMonoidHom

@[simp]

Depends on / 依赖: mapRange, mapRange.equiv, map_zero
-/
def mapRange.addEquiv (em' : M ≃+ N) : (ι ->₀ M) ≃+ (ι ->₀ N) where
  toEquiv := mapRange.equiv em' em'.map_zero
  __ := mapRange.addMonoidHom em'.toAddMonoidHom

@[simp]
/--
lemma `mapRange.addEquiv_refl` / 引理 `mapRange.addEquiv_refl`

English:
lemma mapRange.addEquiv_refl
  statement: mapRange.addEquiv (.refl M) = .refl (ι ->₀ M)
  proof: by ext; simp

中文:
引理 mapRange.addEquiv_refl
  结论: mapRange.addEquiv (.refl M) = .refl (ι ->₀ M)
  证明: by ext; simp
-/
lemma mapRange.addEquiv_refl : mapRange.addEquiv (.refl M) = .refl (ι ->₀ M) := by ext; simp

/--
lemma `mapRange.addEquiv_trans` / 引理 `mapRange.addEquiv_trans`

English:
lemma mapRange.addEquiv_trans
  given: (e₁ : M ≃+ N) (e₂ : N ≃+ O)
  proof: by ext; simp

@[simp]

中文:
引理 mapRange.addEquiv_trans
  条件: (e₁ : M ≃+ N) (e₂ : N ≃+ O)
  证明: by ext; simp

@[simp]
-/
lemma mapRange.addEquiv_trans (e₁ : M ≃+ N) (e₂ : N ≃+ O) :
    mapRange.addEquiv (ι := ι) (e₁.trans e₂) =
      (mapRange.addEquiv e₁).trans (mapRange.addEquiv e₂) := by ext; simp

@[simp]
/--
lemma `mapRange.addEquiv_symm` / 引理 `mapRange.addEquiv_symm`

English:
lemma mapRange.addEquiv_symm
  given: (e : M ≃+ N)
  proof: rfl

@[simp]

中文:
引理 mapRange.addEquiv_symm
  条件: (e : M ≃+ N)
  证明: rfl

@[simp]

Depends on / 依赖: addEquiv, e.symm, mapRange, mapRange.addEquiv
-/
lemma mapRange.addEquiv_symm (e : M ≃+ N) :
    (mapRange.addEquiv (ι := ι) e).symm = mapRange.addEquiv e.symm := rfl

@[simp]
/--
lemma `mapRange.addEquiv_toAddMonoidHom` / 引理 `mapRange.addEquiv_toAddMonoidHom`

English:
lemma mapRange.addEquiv_toAddMonoidHom
  given: (e : M ≃+ N)
  proof: rfl

@[simp]

中文:
引理 mapRange.addEquiv_toAddMonoidHom
  条件: (e : M ≃+ N)
  证明: rfl

@[simp]

Depends on / 依赖: addMonoidHom, e.toAddMonoidHom, mapRange, mapRange.addMonoidHom, toAddMonoidHom
-/
lemma mapRange.addEquiv_toAddMonoidHom (e : M ≃+ N) :
    mapRange.addEquiv (ι := ι) e = mapRange.addMonoidHom (ι := ι) e.toAddMonoidHom := rfl

@[simp]
/--
lemma `mapRange.addEquiv_toEquiv` / 引理 `mapRange.addEquiv_toEquiv`

English:
lemma mapRange.addEquiv_toEquiv
  given: (e : M ≃+ N)
  proof: rfl

中文:
引理 mapRange.addEquiv_toEquiv
  条件: (e : M ≃+ N)
  证明: rfl

Depends on / 依赖: e.map_zero, mapRange, mapRange.equiv, map_zero
-/
lemma mapRange.addEquiv_toEquiv (e : M ≃+ N) :
    mapRange.addEquiv (ι := ι) e = mapRange.equiv (ι := ι) (e : M ≃ N) e.map_zero := rfl

end AddCommMonoid

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [NegZeroClass G]
  body: mapRange Neg.neg neg_zero

中文:
实例 instNeg
  签名: [NegZero类 G]
  定义体: mapRange Neg.neg neg_zero

Depends on / 依赖: Neg.neg, mapRange, neg_zero
-/
instance instNeg [NegZeroClass G] : Neg (ι ->₀ G) where neg := mapRange Neg.neg neg_zero

/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: [NegZeroClass G] (g : ι ->₀ G)
  statement: ⇑(-g) = -g
  proof: rfl

中文:
引理 coe_neg
  条件: [NegZero类 G] (g : ι ->₀ G)
  结论: ⇑(-g) = -g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_neg [NegZeroClass G] (g : ι ->₀ G) : ⇑(-g) = -g := rfl

/--
lemma `neg_apply` / 引理 `neg_apply`

English:
lemma neg_apply
  given: [NegZeroClass G] (g : ι ->₀ G) (a : ι)
  statement: (-g) a = -g a
  proof: rfl

中文:
引理 neg_apply
  条件: [NegZero类 G] (g : ι ->₀ G) (a : ι)
  结论: (-g) a = -g a
  证明: rfl
-/
lemma neg_apply [NegZeroClass G] (g : ι ->₀ G) (a : ι) : (-g) a = -g a :=
  rfl

/--
lemma `mapRange_neg` / 引理 `mapRange_neg`

English:
lemma mapRange_neg
  statement: [NegZeroClass G] [NegZeroClass H] {f : G -> H} {hf : f 0 = 0}
  proof: ext fun _ => by simp only [hf', neg_apply, mapRange_apply]

中文:
引理 mapRange_neg
  结论: [NegZero类 G] [NegZero类 H] {f : G -> H} {hf : f 0 = 0}
  证明: ext fun _ => by simp only [hf', neg_apply, mapRange_apply]

Depends on / 依赖: mapRange_apply, neg_apply
-/
lemma mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G -> H} {hf : f 0 = 0}
    (hf' : forall x, f (-x) = -f x) (v : ι ->₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, mapRange_apply]

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: [SubNegZeroMonoid G]
  body: ⟨zipWith Sub.sub (sub_zero _)⟩

中文:
实例 instSub
  签名: [SubNegZero幺半群 G]
  定义体: ⟨zipWith Sub.sub (sub_zero _)⟩

Depends on / 依赖: Sub.sub, sub_zero, zipWith
-/
instance instSub [SubNegZeroMonoid G] : Sub (ι ->₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩

/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G)
  statement: ⇑(g₁ - g₂) = g₁ - g₂
  proof: rfl

中文:
引理 coe_sub
  条件: [SubNegZero幺半群 G] (g₁ g₂ : ι ->₀ G)
  结论: ⇑(g₁ - g₂) = g₁ - g₂
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sub [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl

/--
lemma `sub_apply` / 引理 `sub_apply`

English:
lemma sub_apply
  given: [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G) (a : ι)
  statement: (g₁ - g₂) a = g₁ a - g₂ a
  proof: rfl

中文:
引理 sub_apply
  条件: [SubNegZero幺半群 G] (g₁ g₂ : ι ->₀ G) (a : ι)
  结论: (g₁ - g₂) a = g₁ a - g₂ a
  证明: rfl
-/
lemma sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

/--
lemma `mapRange_sub` / 引理 `mapRange_sub`

English:
lemma mapRange_sub
  statement: [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G -> H} {hf : f 0 = 0}
  proof: ext fun _ => by simp only [hf', sub_apply, mapRange_apply]

中文:
引理 mapRange_sub
  结论: [SubNegZero幺半群 G] [SubNegZero幺半群 H] {f : G -> H} {hf : f 0 = 0}
  证明: ext fun _ => by simp only [hf', sub_apply, mapRange_apply]

Depends on / 依赖: mapRange_apply, sub_apply
-/
lemma mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G -> H} {hf : f 0 = 0}
    (hf' : forall x y, f (x - y) = f x - f y) (v₁ v₂ : ι ->₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, mapRange_apply]

section AddGroup
variable [AddGroup G] {p : ι -> Prop} {v v' : ι ->₀ G}

/--
lemma `mapRange_neg'` / 引理 `mapRange_neg'`

English:
lemma mapRange_neg'
  statement: [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
  proof: mapRange_neg (map_neg f) v

中文:
引理 mapRange_neg'
  结论: [Subtraction幺半群 H] [函数状 F G H] [加法幺半群态射类 F G H]
  证明: mapRange_neg (map_neg f) v

Depends on / 依赖: mapRange_neg, map_neg
-/
lemma mapRange_neg' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v : ι ->₀ G) :
    mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v

/--
lemma `mapRange_sub'` / 引理 `mapRange_sub'`

English:
lemma mapRange_sub'
  statement: [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
  proof: mapRange_sub (map_sub f) v₁ v₂

中文:
引理 mapRange_sub'
  结论: [Subtraction幺半群 H] [函数状 F G H] [加法幺半群态射类 F G H]
  证明: mapRange_sub (map_sub f) v₁ v₂

Depends on / 依赖: mapRange_sub, map_sub
-/
lemma mapRange_sub' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v₁ v₂ : ι ->₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂

/--
Instance `instIntSMul` / 实例 `instIntSMul`

English:
instance instIntSMul
  signature: : SMul Int (ι ->₀ G)
  body: ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩

中文:
实例 inst整数SMul
  签名: : 标量乘法 整数 (ι ->₀ G)
  定义体: ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩

Depends on / 依赖: mapRange, v.mapRange, zsmul_zero
-/
instance instIntSMul : SMul Int (ι ->₀ G) :=
  ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: : AddGroup (ι ->₀ G)
  body: fast_instance% DFunLike.coe_injective.addGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]

中文:
实例 instAddGroup
  签名: : 加法群 (ι ->₀ G)
  定义体: fast_instance% DFunLike.coe_injective.addGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.addGroup, addGroup, coe_add, coe_injective, coe_neg, coe_sub, coe_zero, fast_instance
-/
instance instAddGroup : AddGroup (ι ->₀ G) :=
  fast_instance% DFunLike.coe_injective.addGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]
/--
lemma `support_neg` / 引理 `support_neg`

English:
lemma support_neg
  given: (f : ι ->₀ G)
  statement: support (-f) = support f
  proof: Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ subseteq support (-f) := support_mapRange)

中文:
引理 support_neg
  条件: (f : ι ->₀ G)
  结论: support (-f) = support f
  证明: Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ subseteq support (-f) := support_mapRange)

Depends on / 依赖: Finset, Finset.Subset.antisymm, Subset, antisymm, congr_arg, neg_neg, subseteq, support, support_mapRange
-/
lemma support_neg (f : ι ->₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ subseteq support (-f) := support_mapRange)

/--
lemma `support_sub` / 引理 `support_sub`

English:
lemma support_sub
  given: [DecidableEq ι] {f g : ι ->₀ G}
  statement: support (f - g) subseteq support f union support g
  proof: by
  rw [sub_eq_add_neg]; rw [← support_neg g]
  exact support_add

中文:
引理 support_sub
  条件: [DecidableEq ι] {f g : ι ->₀ G}
  结论: support (f - g) subseteq support f union support g
  证明: by
  rw [sub_eq_add_neg]; rw [← support_neg g]
  exact support_add

Depends on / 依赖: sub_eq_add_neg, support_add, support_neg
-/
lemma support_sub [DecidableEq ι] {f g : ι ->₀ G} : support (f - g) subseteq support f union support g := by
  rw [sub_eq_add_neg]; rw [← support_neg g]
  exact support_add

/--
lemma `erase_eq_sub_single` / 引理 `erase_eq_sub_single`

English:
lemma erase_eq_sub_single
  given: (f : ι ->₀ G) (a : ι)
  statement: f.erase a = f - single a (f a)
  proof: by
  ext a'
  rcases eq_or_ne a' a with (rfl | h)
  · simp
  · simp [h]

中文:
引理 erase_eq_sub_single
  条件: (f : ι ->₀ G) (a : ι)
  结论: f.erase a = f - single a (f a)
  证明: by
  ext a'
  rcases eq_or_ne a' a with (rfl | h)
  · simp
  · simp [h]

Depends on / 依赖: eq_or_ne
-/
lemma erase_eq_sub_single (f : ι ->₀ G) (a : ι) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a' a with (rfl | h)
  · simp
  · simp [h]

/--
lemma `update_eq_sub_add_single` / 引理 `update_eq_sub_add_single`

English:
lemma update_eq_sub_add_single
  given: (f : ι ->₀ G) (a : ι) (b : G)
  proof: by
  rw [update_eq_erase_add_single]; rw [erase_eq_sub_single]

@[simp]

中文:
引理 update_eq_sub_add_single
  条件: (f : ι ->₀ G) (a : ι) (b : G)
  证明: by
  rw [update_eq_erase_add_single]; rw [erase_eq_sub_single]

@[simp]

Depends on / 依赖: erase_eq_sub_single, update_eq_erase_add_single
-/
lemma update_eq_sub_add_single (f : ι ->₀ G) (a : ι) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single]; rw [erase_eq_sub_single]

@[simp]
/--
lemma `single_neg` / 引理 `single_neg`

English:
lemma single_neg
  given: (a : ι) (b : G)
  statement: single a (-b) = -single a b
  proof: (singleAddHom a : G ->+ _).map_neg b

@[simp]

中文:
引理 single_neg
  条件: (a : ι) (b : G)
  结论: single a (-b) = -single a b
  证明: (singleAddHom a : G ->+ _).map_neg b

@[simp]

Depends on / 依赖: map_neg, singleAddHom
-/
lemma single_neg (a : ι) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G ->+ _).map_neg b

@[simp]
/--
lemma `single_sub` / 引理 `single_sub`

English:
lemma single_sub
  given: (a : ι) (b₁ b₂ : G)
  statement: single a (b₁ - b₂) = single a b₁ - single a b₂
  proof: (singleAddHom a : G ->+ _).map_sub b₁ b₂

@[simp]

中文:
引理 single_sub
  条件: (a : ι) (b₁ b₂ : G)
  结论: single a (b₁ - b₂) = single a b₁ - single a b₂
  证明: (singleAddHom a : G ->+ _).map_sub b₁ b₂

@[simp]

Depends on / 依赖: map_sub, singleAddHom
-/
lemma single_sub (a : ι) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G ->+ _).map_sub b₁ b₂

@[simp]
/--
lemma `erase_neg` / 引理 `erase_neg`

English:
lemma erase_neg
  given: (a : ι) (f : ι ->₀ G)
  statement: erase a (-f) = -erase a f
  proof: (eraseAddHom a : (_ ->₀ G) ->+ _).map_neg f

@[simp]

中文:
引理 erase_neg
  条件: (a : ι) (f : ι ->₀ G)
  结论: erase a (-f) = -erase a f
  证明: (eraseAddHom a : (_ ->₀ G) ->+ _).map_neg f

@[simp]

Depends on / 依赖: eraseAddHom, map_neg
-/
lemma erase_neg (a : ι) (f : ι ->₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ ->₀ G) ->+ _).map_neg f

@[simp]
/--
lemma `erase_sub` / 引理 `erase_sub`

English:
lemma erase_sub
  given: (a : ι) (f₁ f₂ : ι ->₀ G)
  statement: erase a (f₁ - f₂) = erase a f₁ - erase a f₂
  proof: (eraseAddHom a : (_ ->₀ G) ->+ _).map_sub f₁ f₂

中文:
引理 erase_sub
  条件: (a : ι) (f₁ f₂ : ι ->₀ G)
  结论: erase a (f₁ - f₂) = erase a f₁ - erase a f₂
  证明: (eraseAddHom a : (_ ->₀ G) ->+ _).map_sub f₁ f₂

Depends on / 依赖: eraseAddHom, map_sub
-/
lemma erase_sub (a : ι) (f₁ f₂ : ι ->₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ ->₀ G) ->+ _).map_sub f₁ f₂

end AddGroup

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup G]
  body: fast_instance% DFunLike.coe_injective.addCommGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddCommGroup
  签名: [加法交换群 G]
  定义体: fast_instance% DFunLike.coe_injective.addCommGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.addCommGroup, addCommGroup, coe_add, coe_injective, coe_neg, coe_sub, coe_zero, fast_instance
-/
instance instAddCommGroup [AddCommGroup G] : AddCommGroup (ι ->₀ G) :=
  fast_instance% DFunLike.coe_injective.addCommGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

end Finsupp
