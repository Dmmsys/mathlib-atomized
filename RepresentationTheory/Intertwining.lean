/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov, Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Intertwining maps

This file gives defines intertwining maps of representations (aka equivariant linear maps).

-/

@[expose] public section

open scoped MonoidAlgebra

namespace Representation

section non_comm
section Monoid

variable {A G V W U : Type*} [Semiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V ->ₗ[A] W)

/--
Definition of `IsIntertwiningMap` / `IsIntertwiningMap` 的定义

English:
structure IsIntertwiningMap
  parameters: : Prop where
  axioms and operations (1):
    - isIntertwining((g : G) (v : V)) : f (ρ g v) = σ g (f v)

中文:
结构 是整数ertwining映射
  参数: : 命题 where
  公理与运算 (1 个):
    - isIntertwining((g : G) (v : V)) : f (ρ g v) = σ g (f v)
-/
@[mk_iff] structure IsIntertwiningMap : Prop where
  isIntertwining (g : G) (v : V) : f (ρ g v) = σ g (f v)

/--
Definition of `IntertwiningMap` / `IntertwiningMap` 的定义

English:
structure IntertwiningMap
  parameters: extends V ->ₗ[A] W
  extends: V ->ₗ[A] W
  axioms and operations (1):
    - isIntertwining'((g : G)) : toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap

中文:
结构 整数ertwining映射
  参数: extends V ->ₗ[A] W
  继承: V ->ₗ[A] W
  公理与运算 (1 个):
    - isIntertwining'((g : G)) : toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap
-/
structure IntertwiningMap extends V ->ₗ[A] W where
  /-- An underlying `A`-linear map of the underlying `A`-modules. -/
  isIntertwining' (g : G) : toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap

/--
Definition of `_root_.LinearMap.intertwiningMap_of_isIntertwiningMap` / `_root_.LinearMap.intertwiningMap_of_isIntertwiningMap` 的定义

English:
definition _root_.LinearMap.intertwiningMap_of_isIntertwiningMap
  body: { f with isIntertwining' g := by ext v; exact hf g v }

中文:
定义 _root_.线性映射.intertwiningMap_of_is整数ertwiningMap
  定义体: { f with isIntertwining' g := by ext v; exact hf g v }

Depends on / 依赖: isIntertwining
-/
def _root_.LinearMap.intertwiningMap_of_isIntertwiningMap
    (hf : forall (g : G), forall (v : V), f (ρ g v) = σ g (f v)) : IntertwiningMap ρ σ :=
  { f with isIntertwining' g := by ext v; exact hf g v }

/--
lemma `IntertwiningMap.isIntertwining_assoc` / 引理 `IntertwiningMap.isIntertwining_assoc`

English:
lemma IntertwiningMap.isIntertwining_assoc
  given: {f : IntertwiningMap ρ σ} (g : G) (l : U ->ₗ[A] V)
  proof: by
  rw [← LinearMap.comp_assoc]; rw [f.2]; rw [LinearMap.comp_assoc]

中文:
引理 整数ertwining映射.is整数ertwining_assoc
  条件: {f : 整数ertwining映射 ρ σ} (g : G) (l : U ->ₗ[A] V)
  证明: by
  rw [← LinearMap.comp_assoc]; rw [f.2]; rw [LinearMap.comp_assoc]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc
-/
lemma IntertwiningMap.isIntertwining_assoc {f : IntertwiningMap ρ σ} (g : G) (l : U ->ₗ[A] V) :
    f.toLinearMap ∘ₗ ρ g ∘ₗ l = σ g ∘ₗ f.toLinearMap ∘ₗ l := by
  rw [← LinearMap.comp_assoc]; rw [f.2]; rw [LinearMap.comp_assoc]

namespace IntertwiningMap

variable {ρ σ} in
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap)
  statement: f = g
  proof: by
  cases f; cases g
  simpa using h

中文:
引理 ext
  条件: {f g : 整数ertwining映射 ρ σ} (h : f.toLinearMap = g.toLinearMap)
  结论: f = g
  证明: by
  cases f; cases g
  simpa using h
-/
lemma ext {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g
  simpa using h

/--
lemma `toLinearMap_injective` / 引理 `toLinearMap_injective`

English:
lemma toLinearMap_injective
  statement: Function.Injective fun f : IntertwiningMap ρ σ => f.toLinearMap
  proof: fun _ _ => ext

中文:
引理 toLinearMap_injective
  结论: 函数.单射 fun f : 整数ertwining映射 ρ σ => f.toLinearMap
  证明: fun _ _ => ext
-/
lemma toLinearMap_injective : Function.Injective fun f : IntertwiningMap ρ σ => f.toLinearMap :=
  fun _ _ => ext

/--
lemma `toFun_injective` / 引理 `toFun_injective`

English:
lemma toFun_injective
  statement: Function.Injective fun f : IntertwiningMap ρ σ => f.toLinearMap.toFun
  proof: by
  intro f g h
  ext x
  exact congrFun h x

中文:
引理 toFun_injective
  结论: 函数.单射 fun f : 整数ertwining映射 ρ σ => f.toLinearMap.toFun
  证明: by
  intro f g h
  ext x
  exact congrFun h x
-/
lemma toFun_injective : Function.Injective fun f : IntertwiningMap ρ σ => f.toLinearMap.toFun := by
  intro f g h
  ext x
  exact congrFun h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (IntertwiningMap ρ σ) V W
  body: f.toFun
  coe_injective := toFun_injective ρ σ

中文:
实例 :
  签名: 函数状 (整数ertwining映射 ρ σ) V W
  定义体: f.toFun
  coe_injective := toFun_injective ρ σ

Depends on / 依赖: f.toFun
-/
instance : FunLike (IntertwiningMap ρ σ) V W where
  coe f := f.toFun
  coe_injective := toFun_injective ρ σ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (IntertwiningMap ρ σ) A V W
  body: f.map_add
  map_smulₛₗ f := f.map_smul

中文:
实例 :
  签名: 线性映射类 (整数ertwining映射 ρ σ) A V W
  定义体: f.map_add
  map_smulₛₗ f := f.map_smul

Depends on / 依赖: f.map_add, map_add
-/
instance : LinearMapClass (IntertwiningMap ρ σ) A V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

-- Despite the other bundled homs having the inverse direction as simp lemmas,
-- we are actively moving away from these design decisions.
-- See e.g. https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Concrete.20homomorphism.20type.20vs.20abstract.20class/with/492579416
@[simp]
/--
lemma `coe_eq_toLinearMap` / 引理 `coe_eq_toLinearMap`

English:
lemma coe_eq_toLinearMap
  given: {f : IntertwiningMap ρ σ}
  proof: rfl

中文:
引理 coe_eq_toLinearMap
  条件: {f : 整数ertwining映射 ρ σ}
  证明: rfl
-/
lemma coe_eq_toLinearMap {f : IntertwiningMap ρ σ} :
  SemilinearMapClass.semilinearMap f = f.toLinearMap := rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : V ->ₗ[A] W) (h)
  statement: ⇑(⟨f, h⟩ : IntertwiningMap ρ σ) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : V ->ₗ[A] W) (h)
  结论: ⇑(⟨f, h⟩ : 整数ertwining映射 ρ σ) = f
  证明: rfl
-/
@[simp] theorem coe_mk (f : V ->ₗ[A] W) (h) : ⇑(⟨f, h⟩ : IntertwiningMap ρ σ) = f := rfl

/--
lemma `toLinearMap_mk` / 引理 `toLinearMap_mk`

English:
lemma toLinearMap_mk
  given: (f : V ->ₗ[A] W) (h)
  proof: rfl

中文:
引理 toLinearMap_mk
  条件: (f : V ->ₗ[A] W) (h)
  证明: rfl
-/
lemma toLinearMap_mk (f : V ->ₗ[A] W) (h) :
  (⟨f, h⟩ : IntertwiningMap ρ σ).toLinearMap = f := rfl

/--
lemma `isIntertwining` / 引理 `isIntertwining`

English:
lemma isIntertwining
  given: (f : IntertwiningMap ρ σ) (g : G) (v : V)
  proof: congr($(f.isIntertwining' g) v)

中文:
引理 is整数ertwining
  条件: (f : 整数ertwining映射 ρ σ) (g : G) (v : V)
  证明: congr($(f.isIntertwining' g) v)

Depends on / 依赖: f.isIntertwining, isIntertwining
-/
lemma isIntertwining (f : IntertwiningMap ρ σ) (g : G) (v : V) :
    f (ρ g v) = σ g (f v) := congr($(f.isIntertwining' g) v)

/--
lemma `toLinearMap_apply` / 引理 `toLinearMap_apply`

English:
lemma toLinearMap_apply
  given: (f : IntertwiningMap ρ σ) (v : V)
  statement: f.toLinearMap v = f v
  proof: rfl

中文:
引理 toLinearMap_apply
  条件: (f : 整数ertwining映射 ρ σ) (v : V)
  结论: f.toLinearMap v = f v
  证明: rfl
-/
lemma toLinearMap_apply (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v := rfl

/--
lemma `coe_toLinearMap` / 引理 `coe_toLinearMap`

English:
lemma coe_toLinearMap
  given: (f : IntertwiningMap ρ σ)
  statement: (f.toLinearMap : _ -> _) = f
  proof: rfl

中文:
引理 coe_toLinearMap
  条件: (f : 整数ertwining映射 ρ σ)
  结论: (f.toLinearMap : _ -> _) = f
  证明: rfl
-/
@[simp] lemma coe_toLinearMap (f : IntertwiningMap ρ σ) : (f.toLinearMap : _ -> _) = f := rfl

/--
lemma `_root_.LinearMap.toIntertwiningMap` / 引理 `_root_.LinearMap.toIntertwiningMap`

English:
lemma _root_.LinearMap.toIntertwiningMap
  proof: rfl

中文:
引理 _root_.线性映射.to整数ertwiningMap
  证明: rfl
-/
@[simp] lemma _root_.LinearMap.toIntertwiningMap
  (hf : forall (g : G), forall (v : V), f (ρ g v) = σ g (f v)) (v : V) :
  f.intertwiningMap_of_isIntertwiningMap ρ σ hf v = f v := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (IntertwiningMap ρ σ)
  body: ⟨⟨0, by simp⟩⟩

中文:
实例 :
  签名: 零 (整数ertwining映射 ρ σ)
  定义体: ⟨⟨0, by simp⟩⟩
-/
instance : Zero (IntertwiningMap ρ σ) := ⟨⟨0, by simp⟩⟩

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ((0 : IntertwiningMap ρ σ) : V -> W) = 0
  proof: rfl

中文:
引理 coe_zero
  结论: ((0 : 整数ertwining映射 ρ σ) : V -> W) = 0
  证明: rfl
-/
@[simp] lemma coe_zero : ((0 : IntertwiningMap ρ σ) : V -> W) = 0 := rfl

/--
lemma `zero_toLinearMap` / 引理 `zero_toLinearMap`

English:
lemma zero_toLinearMap
  statement: (0 : IntertwiningMap ρ σ).toLinearMap = 0
  proof: rfl

中文:
引理 zero_toLinearMap
  结论: (0 : 整数ertwining映射 ρ σ).toLinearMap = 0
  证明: rfl
-/
@[simp] lemma zero_toLinearMap : (0 : IntertwiningMap ρ σ).toLinearMap = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (IntertwiningMap ρ σ)
  body: ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap, by
    simp [LinearMap.add_comp, LinearMap.comp_add, f.2, g.2,]⟩⟩

中文:
实例 :
  签名: 加法 (整数ertwining映射 ρ σ)
  定义体: ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap, by
    simp [LinearMap.add_comp, LinearMap.comp_add, f.2, g.2,]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.add_comp, LinearMap.comp_add, add_comp, comp_add, f.toLinearMap, g.toLinearMap, toLinearMap
-/
instance : Add (IntertwiningMap ρ σ) :=
  ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap, by
    simp [LinearMap.add_comp, LinearMap.comp_add, f.2, g.2,]⟩⟩

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (f g : IntertwiningMap ρ σ)
  proof: rfl

@[simp]

中文:
引理 coe_add
  条件: (f g : 整数ertwining映射 ρ σ)
  证明: rfl

@[simp]
-/
@[simp] lemma coe_add (f g : IntertwiningMap ρ σ) :
    ((f + g : IntertwiningMap ρ σ) : V -> W) = f + g := rfl

@[simp]
/--
lemma `add_toLinearMap` / 引理 `add_toLinearMap`

English:
lemma add_toLinearMap
  given: (f g : IntertwiningMap ρ σ)
  proof: rfl

中文:
引理 add_toLinearMap
  条件: (f g : 整数ertwining映射 ρ σ)
  证明: rfl
-/
lemma add_toLinearMap (f g : IntertwiningMap ρ σ) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (IntertwiningMap ρ σ)
  body: ⟨fun n f => ⟨n • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

中文:
实例 :
  签名: 标量乘法 自然数 (整数ertwining映射 ρ σ)
  定义体: ⟨fun n f => ⟨n • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.comp_smul, LinearMap.smul_comp, comp_smul, f.toLinearMap, smul_comp, toLinearMap
-/
instance : SMul Nat (IntertwiningMap ρ σ) :=
  ⟨fun n f => ⟨n • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (f : IntertwiningMap ρ σ) (n : Nat)
  proof: rfl

中文:
引理 coe_nsmul
  条件: (f : 整数ertwining映射 ρ σ) (n : 自然数)
  证明: rfl
-/
@[simp] lemma coe_nsmul (f : IntertwiningMap ρ σ) (n : Nat) :
    ((n • f : IntertwiningMap ρ σ) : V -> W) = n • f := rfl

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (IntertwiningMap ρ σ)
  body: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (整数ertwining映射 ρ σ)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommMonoid, addCommMonoid, coe_add, coe_injective, coe_nsmul, coe_zero, fast_instance
-/
instance instAddCommMonoid : AddCommMonoid (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

/-- The range of an intertwining map from `V` to `W` as a subrepresentation of `W`. -/
@[simps]
/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : IntertwiningMap ρ σ)
  body: LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g {w} := fun ⟨v, hv⟩ => ⟨(ρ g) v, by
    simp [f.isIntertwining, (f.toLinearMap_apply _ _ _).symm.trans hv]⟩

@[simp]

中文:
定义 range
  签名: (f : 整数ertwining映射 ρ σ)
  定义体: LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g {w} := fun ⟨v, hv⟩ => ⟨(ρ g) v, by
    simp [f.isIntertwining, (f.toLinearMap_apply _ _ _).symm.trans hv]⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range, f.toLinearMap, toLinearMap
-/
def range (f : IntertwiningMap ρ σ) : Subrepresentation σ where
  toSubmodule := LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g {w} := fun ⟨v, hv⟩ => ⟨(ρ g) v, by
    simp [f.isIntertwining, (f.toLinearMap_apply _ _ _).symm.trans hv]⟩

@[simp]
/--
lemma `mem_range` / 引理 `mem_range`

English:
lemma mem_range
  given: (f : IntertwiningMap ρ σ) (w : W)
  proof: Iff.rfl

中文:
引理 mem_range
  条件: (f : 整数ertwining映射 ρ σ) (w : W)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_range (f : IntertwiningMap ρ σ) (w : W) :
    w in f.range ↔ exists v, f v = w := Iff.rfl

/-- The kernel of an intertwining map from `V` to `W` as a subrepresentation of `V`. -/
@[simps]
/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : IntertwiningMap ρ σ)
  body: LinearMap.ker f.toLinearMap
  apply_mem_toSubmodule g := by simp +contextual [f.isIntertwining]

@[simp]

中文:
定义 ker
  签名: (f : 整数ertwining映射 ρ σ)
  定义体: LinearMap.ker f.toLinearMap
  apply_mem_toSubmodule g := by simp +contextual [f.isIntertwining]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ker, f.toLinearMap, toLinearMap
-/
def ker (f : IntertwiningMap ρ σ) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker f.toLinearMap
  apply_mem_toSubmodule g := by simp +contextual [f.isIntertwining]

@[simp]
/--
lemma `mem_ker` / 引理 `mem_ker`

English:
lemma mem_ker
  given: (f : IntertwiningMap ρ σ) (v : V)
  proof: Iff.rfl

中文:
引理 mem_ker
  条件: (f : 整数ertwining映射 ρ σ) (v : V)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_ker (f : IntertwiningMap ρ σ) (v : V) :
    v in f.ker ↔ f v = 0 := Iff.rfl

/--
lemma `toLinearMap_sum` / 引理 `toLinearMap_sum`

English:
lemma toLinearMap_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ)
  proof: by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

中文:
引理 toLinearMap_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 整数ertwining映射 ρ σ)
  证明: by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, classical, insert, sum_insert
-/
lemma toLinearMap_sum {ι : Type*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ) :
    (∑ i in s, f i : IntertwiningMap ρ σ).toLinearMap = ∑ i in s, (f i).toLinearMap := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/--
lemma `sum_apply` / 引理 `sum_apply`

English:
lemma sum_apply
  given: {ι : Type*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ) (v : V)
  proof: by
  simp [← toLinearMap_apply _ _ (∑ _ in s, _), toLinearMap_sum, LinearMap.sum_apply]

中文:
引理 sum_apply
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 整数ertwining映射 ρ σ) (v : V)
  证明: by
  simp [← toLinearMap_apply _ _ (∑ _ in s, _), toLinearMap_sum, LinearMap.sum_apply]

Depends on / 依赖: LinearMap, LinearMap.sum_apply, sum_apply, toLinearMap_apply, toLinearMap_sum
-/
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ) (v : V) :
    (∑ i in s, f i) v = ∑ i in s, f i v := by
  simp [← toLinearMap_apply _ _ (∑ _ in s, _), toLinearMap_sum, LinearMap.sum_apply]

section group

variable {V W P : Type*} [AddCommMonoid V] [AddCommGroup W]
  [AddCommGroup P] [Module A V] [Module A W] [Module A P] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G P) (f : V ->ₗ[A] W)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (IntertwiningMap ρ σ)
  body: ⟨fun f => ⟨-f.toLinearMap, by simp [LinearMap.neg_comp, f.2]⟩⟩

@[simp]

中文:
实例 :
  签名: 取负 (整数ertwining映射 ρ σ)
  定义体: ⟨fun f => ⟨-f.toLinearMap, by simp [LinearMap.neg_comp, f.2]⟩⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.neg_comp, f.toLinearMap, neg_comp, toLinearMap
-/
instance : Neg (IntertwiningMap ρ σ) :=
  ⟨fun f => ⟨-f.toLinearMap, by simp [LinearMap.neg_comp, f.2]⟩⟩

@[simp]
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (f : IntertwiningMap ρ σ)
  statement: ((-f : IntertwiningMap ρ σ) : V -> W) = -f
  proof: rfl

中文:
引理 coe_neg
  条件: (f : 整数ertwining映射 ρ σ)
  结论: ((-f : 整数ertwining映射 ρ σ) : V -> W) = -f
  证明: rfl
-/
lemma coe_neg (f : IntertwiningMap ρ σ) : ((-f : IntertwiningMap ρ σ) : V -> W) = -f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (IntertwiningMap ρ σ)
  body: ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap, by
    simp [LinearMap.sub_comp, LinearMap.comp_sub, f.2, g.2]⟩⟩

中文:
实例 :
  签名: 减法 (整数ertwining映射 ρ σ)
  定义体: ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap, by
    simp [LinearMap.sub_comp, LinearMap.comp_sub, f.2, g.2]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.comp_sub, LinearMap.sub_comp, comp_sub, f.toLinearMap, g.toLinearMap, sub_comp, toLinearMap
-/
instance : Sub (IntertwiningMap ρ σ) :=
  ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap, by
    simp [LinearMap.sub_comp, LinearMap.comp_sub, f.2, g.2]⟩⟩

/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (f g : IntertwiningMap ρ σ)
  proof: rfl

@[simp]

中文:
引理 coe_sub
  条件: (f g : 整数ertwining映射 ρ σ)
  证明: rfl

@[simp]
-/
@[simp] lemma coe_sub (f g : IntertwiningMap ρ σ) :
    ((f - g : IntertwiningMap ρ σ) : V -> W) = f - g := rfl

@[simp]
/--
lemma `sub_toLinearMap` / 引理 `sub_toLinearMap`

English:
lemma sub_toLinearMap
  given: (f g : IntertwiningMap ρ σ)
  proof: rfl

中文:
引理 sub_toLinearMap
  条件: (f g : 整数ertwining映射 ρ σ)
  证明: rfl
-/
lemma sub_toLinearMap (f g : IntertwiningMap ρ σ) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (IntertwiningMap ρ σ)
  body: ⟨fun z f => ⟨z • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

中文:
实例 :
  签名: 标量乘法 整数 (整数ertwining映射 ρ σ)
  定义体: ⟨fun z f => ⟨z • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.comp_smul, LinearMap.smul_comp, comp_smul, f.toLinearMap, smul_comp, toLinearMap
-/
instance : SMul Int (IntertwiningMap ρ σ) :=
  ⟨fun z f => ⟨z • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

/--
lemma `coe_zsmul` / 引理 `coe_zsmul`

English:
lemma coe_zsmul
  given: (f : IntertwiningMap ρ σ) (z : Int)
  proof: rfl

中文:
引理 coe_zsmul
  条件: (f : 整数ertwining映射 ρ σ) (z : 整数)
  证明: rfl
-/
@[simp] lemma coe_zsmul (f : IntertwiningMap ρ σ) (z : Int) :
    ((z • f : IntertwiningMap ρ σ) : V -> W) = z • f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (IntertwiningMap ρ σ)
  body: fast_instance%
  DFunLike.coe_injective.addCommGroup _ (coe_zero ρ σ) (coe_add ρ σ) (coe_neg ρ σ) (coe_sub ρ σ)
    (coe_nsmul ρ σ) (coe_zsmul ρ σ)

中文:
实例 :
  签名: 加法交换群 (整数ertwining映射 ρ σ)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommGroup _ (coe_zero ρ σ) (coe_add ρ σ) (coe_neg ρ σ) (coe_sub ρ σ)
    (coe_nsmul ρ σ) (coe_zsmul ρ σ)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommGroup, addCommGroup, coe_add, coe_injective, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul, fast_instance
-/
instance : AddCommGroup (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommGroup _ (coe_zero ρ σ) (coe_add ρ σ) (coe_neg ρ σ) (coe_sub ρ σ)
    (coe_nsmul ρ σ) (coe_zsmul ρ σ)

end group

/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: : IntertwiningMap ρ σ ->+ V -> W where
  body: (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ

中文:
定义 coeFnAddMonoidHom
  签名: : 整数ertwining映射 ρ σ ->+ V -> W where
  定义体: (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ
-/
def coeFnAddMonoidHom : IntertwiningMap ρ σ ->+ V -> W where
  toFun := (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : IntertwiningMap ρ ρ where
  body: LinearMap.id
  isIntertwining' := by simp

@[simp]

中文:
定义 id
  签名: : 整数ertwining映射 ρ ρ where
  定义体: LinearMap.id
  isIntertwining' := by simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def id : IntertwiningMap ρ ρ where
  toLinearMap := LinearMap.id
  isIntertwining' := by simp

@[simp]
/--
lemma `toLinearMap_id` / 引理 `toLinearMap_id`

English:
lemma toLinearMap_id
  statement: (id ρ).toLinearMap = LinearMap.id
  proof: rfl

@[simp]

中文:
引理 toLinearMap_id
  结论: (id ρ).toLinearMap = 线性映射.id
  证明: rfl

@[simp]
-/
lemma toLinearMap_id : (id ρ).toLinearMap = LinearMap.id := rfl

@[simp]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (v : V)
  statement: id ρ v = v
  proof: rfl

中文:
引理 id_apply
  条件: (v : V)
  结论: id ρ v = v
  证明: rfl
-/
lemma id_apply (v : V) : id ρ v = v := rfl

variable {ρ σ τ} in
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ)
  body: f.toLinearMap ∘ₗ g.toLinearMap
  isIntertwining' := by simp [LinearMap.comp_assoc, g.2, f.isIntertwining_assoc]

@[simp]

中文:
定义 comp
  签名: (f : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ)
  定义体: f.toLinearMap ∘ₗ g.toLinearMap
  isIntertwining' := by simp [LinearMap.comp_assoc, g.2, f.isIntertwining_assoc]

@[simp]

Depends on / 依赖: f.toLinearMap, g.toLinearMap, toLinearMap
-/
def comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : IntertwiningMap ρ τ where
  __ := f.toLinearMap ∘ₗ g.toLinearMap
  isIntertwining' := by simp [LinearMap.comp_assoc, g.2, f.isIntertwining_assoc]

@[simp]
/--
lemma `comp_toLinearMap` / 引理 `comp_toLinearMap`

English:
lemma comp_toLinearMap
  given: (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ)
  proof: rfl

@[simp]

中文:
引理 comp_toLinearMap
  条件: (f : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ)
  证明: rfl

@[simp]
-/
lemma comp_toLinearMap (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (comp f g).toLinearMap = f.toLinearMap.comp g.toLinearMap := rfl

@[simp]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) (v : V)
  proof: rfl

中文:
引理 comp_apply
  条件: (f : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ) (v : V)
  证明: rfl
-/
lemma comp_apply (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) (v : V) :
    comp f g v = f (g v) := rfl

/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  given: (f₁ f₂ : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ)
  proof: by ext1; simp [LinearMap.add_comp]

中文:
引理 comp_add
  条件: (f₁ f₂ : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ)
  证明: by ext1; simp [LinearMap.add_comp]

Depends on / 依赖: LinearMap, LinearMap.add_comp, add_comp
-/
lemma comp_add (f₁ f₂ : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f₁ + f₂).comp g = comp f₁ g + comp f₂ g := by ext1; simp [LinearMap.add_comp]

/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  given: (f : IntertwiningMap σ τ) (g₁ g₂ : IntertwiningMap ρ σ)
  proof: by ext1; simp [LinearMap.comp_add]

中文:
引理 add_comp
  条件: (f : 整数ertwining映射 σ τ) (g₁ g₂ : 整数ertwining映射 ρ σ)
  证明: by ext1; simp [LinearMap.comp_add]

Depends on / 依赖: LinearMap, LinearMap.comp_add, comp_add
-/
lemma add_comp (f : IntertwiningMap σ τ) (g₁ g₂ : IntertwiningMap ρ σ) :
    comp f (g₁ + g₂) = comp f g₁ + comp f g₂ := by ext1; simp [LinearMap.comp_add]

variable (A) in
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : IntertwiningMap (ρ.prod σ) ρ where
  body: LinearMap.fst A V W
isIntertwining' _ := LinearMap.ext by simp

中文:
定义 fst
  签名: : 整数ertwining映射 (ρ.乘积 σ) ρ where
  定义体: LinearMap.fst A V W
isIntertwining' _ := LinearMap.ext by simp

Depends on / 依赖: LinearMap, LinearMap.fst
-/
def fst : IntertwiningMap (ρ.prod σ) ρ where
  toLinearMap := LinearMap.fst A V W
isIntertwining' _ := LinearMap.ext by simp

variable (A) in
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : IntertwiningMap (ρ.prod σ) σ where
  body: LinearMap.snd A V W
isIntertwining' _ := LinearMap.ext by simp

@[simp]

中文:
定义 snd
  签名: : 整数ertwining映射 (ρ.乘积 σ) σ where
  定义体: LinearMap.snd A V W
isIntertwining' _ := LinearMap.ext by simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.snd
-/
def snd : IntertwiningMap (ρ.prod σ) σ where
  toLinearMap := LinearMap.snd A V W
isIntertwining' _ := LinearMap.ext by simp

@[simp]
/--
lemma `fst_apply` / 引理 `fst_apply`

English:
lemma fst_apply
  given: (v : V × W)
  statement: fst A ρ σ v = v.1
  proof: rfl

@[simp]

中文:
引理 fst_apply
  条件: (v : V × W)
  结论: fst A ρ σ v = v.1
  证明: rfl

@[simp]
-/
lemma fst_apply (v : V × W) : fst A ρ σ v = v.1 := rfl

@[simp]
/--
lemma `snd_apply` / 引理 `snd_apply`

English:
lemma snd_apply
  given: (v : V × W)
  statement: snd A ρ σ v = v.2
  proof: rfl

中文:
引理 snd_apply
  条件: (v : V × W)
  结论: snd A ρ σ v = v.2
  证明: rfl
-/
lemma snd_apply (v : V × W) : snd A ρ σ v = v.2 := rfl

/--
lemma `coe_fst` / 引理 `coe_fst`

English:
lemma coe_fst
  statement: ⇑(fst A ρ σ) = Prod.fst
  proof: rfl

中文:
引理 coe_fst
  结论: ⇑(fst A ρ σ) = 积类型.fst
  证明: rfl
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst A ρ σ) = Prod.fst := rfl

/--
lemma `coe_snd` / 引理 `coe_snd`

English:
lemma coe_snd
  statement: ⇑(snd A ρ σ) = Prod.snd
  proof: rfl

中文:
引理 coe_snd
  结论: ⇑(snd A ρ σ) = 积类型.snd
  证明: rfl
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd A ρ σ) = Prod.snd := rfl

/--
lemma `fst_surjective` / 引理 `fst_surjective`

English:
lemma fst_surjective
  statement: Function.Surjective (fst A ρ σ)
  proof: LinearMap.fst_surjective

中文:
引理 fst_surjective
  结论: 函数.满射 (fst A ρ σ)
  证明: LinearMap.fst_surjective

Depends on / 依赖: LinearMap, LinearMap.fst_surjective, fst_surjective
-/
lemma fst_surjective : Function.Surjective (fst A ρ σ) := LinearMap.fst_surjective

/--
lemma `snd_surjective` / 引理 `snd_surjective`

English:
lemma snd_surjective
  statement: Function.Surjective (snd A ρ σ)
  proof: LinearMap.snd_surjective

中文:
引理 snd_surjective
  结论: 函数.满射 (snd A ρ σ)
  证明: LinearMap.snd_surjective

Depends on / 依赖: LinearMap, LinearMap.snd_surjective, snd_surjective
-/
lemma snd_surjective : Function.Surjective (snd A ρ σ) := LinearMap.snd_surjective

section prod

variable {ρ σ τ}
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ)
  body: f.toLinearMap.prod g.toLinearMap
isIntertwining' _ := LinearMap.ext by simp [f.isIntertwining, g.isIntertwining]

@[simp]

中文:
定义 乘积
  签名: (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 ρ τ)
  定义体: f.toLinearMap.prod g.toLinearMap
isIntertwining' _ := LinearMap.ext by simp [f.isIntertwining, g.isIntertwining]

@[simp]

Depends on / 依赖: f.toLinearMap.prod, g.toLinearMap, toLinearMap
-/
def prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) : IntertwiningMap ρ (σ.prod τ) where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
isIntertwining' _ := LinearMap.ext by simp [f.isIntertwining, g.isIntertwining]

@[simp]
/--
lemma `fst_prod` / 引理 `fst_prod`

English:
lemma fst_prod
  given: (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ)
  proof: IntertwiningMap.ext LinearMap.fst_prod _ _

@[simp]

中文:
引理 fst_prod
  条件: (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 ρ τ)
  证明: IntertwiningMap.ext LinearMap.fst_prod _ _

@[simp]

Depends on / 依赖: IntertwiningMap, IntertwiningMap.ext, LinearMap, LinearMap.fst_prod, fst_prod
-/
lemma fst_prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) :
(fst A σ τ).comp (prod f g) = f := IntertwiningMap.ext LinearMap.fst_prod _ _

@[simp]
/--
lemma `snd_prod` / 引理 `snd_prod`

English:
lemma snd_prod
  given: (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ)
  proof: IntertwiningMap.ext LinearMap.snd_prod _ _

中文:
引理 snd_prod
  条件: (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 ρ τ)
  证明: IntertwiningMap.ext LinearMap.snd_prod _ _

Depends on / 依赖: IntertwiningMap, IntertwiningMap.ext, LinearMap, LinearMap.snd_prod, snd_prod
-/
lemma snd_prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) :
(snd A σ τ).comp (prod f g) = g := IntertwiningMap.ext LinearMap.snd_prod _ _

/--
lemma `prod_comp` / 引理 `prod_comp`

English:
lemma prod_comp
  statement: (X : Type*) [AddCommMonoid X] [Module A X] {π : Representation A G X}
  proof: IntertwiningMap.ext LinearMap.prod_comp ..

中文:
引理 prod_comp
  结论: (X : 类型) [加法交换幺半群 X] [模 A X] {π : Representation A G X}
  证明: IntertwiningMap.ext LinearMap.prod_comp ..

Depends on / 依赖: IntertwiningMap, IntertwiningMap.ext, LinearMap, LinearMap.prod_comp, prod_comp
-/
lemma prod_comp (X : Type*) [AddCommMonoid X] [Module A X] {π : Representation A G X}
    (f : IntertwiningMap ρ σ) (g₁ : IntertwiningMap σ τ) (g₂ : IntertwiningMap σ π) :
    (prod g₁ g₂).comp f = prod (g₁.comp f) (g₂.comp f) :=
IntertwiningMap.ext LinearMap.prod_comp ..

variable (A ρ σ) in
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : IntertwiningMap ρ (ρ.prod σ)
  body: prod (id ρ) 0

中文:
定义 inl
  签名: : 整数ertwining映射 ρ (ρ.乘积 σ)
  定义体: prod (id ρ) 0
-/
def inl : IntertwiningMap ρ (ρ.prod σ) := prod (id ρ) 0

variable (A ρ σ) in
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : IntertwiningMap σ (ρ.prod σ)
  body: prod (0 : IntertwiningMap σ ρ) (id σ)

中文:
定义 inr
  签名: : 整数ertwining映射 σ (ρ.乘积 σ)
  定义体: prod (0 : IntertwiningMap σ ρ) (id σ)

Depends on / 依赖: IntertwiningMap
-/
def inr : IntertwiningMap σ (ρ.prod σ) := prod (0 : IntertwiningMap σ ρ) (id σ)

/--
lemma `range_inl` / 引理 `range_inl`

English:
lemma range_inl
  statement: (inl A ρ σ).range = (snd A ρ σ).ker
  proof: Subrepresentation.ext LinearMap.range_inl ..

中文:
引理 range_inl
  结论: (inl A ρ σ).range = (snd A ρ σ).ker
  证明: Subrepresentation.ext LinearMap.range_inl ..

Depends on / 依赖: LinearMap, LinearMap.range_inl, Subrepresentation, Subrepresentation.ext, range_inl
-/
lemma range_inl : (inl A ρ σ).range = (snd A ρ σ).ker :=
Subrepresentation.ext LinearMap.range_inl ..

/--
lemma `range_inr` / 引理 `range_inr`

English:
lemma range_inr
  statement: (inr A ρ σ).range = (fst A ρ σ).ker
  proof: Subrepresentation.ext LinearMap.range_inr ..

中文:
引理 range_inr
  结论: (inr A ρ σ).range = (fst A ρ σ).ker
  证明: Subrepresentation.ext LinearMap.range_inr ..

Depends on / 依赖: LinearMap, LinearMap.range_inr, Subrepresentation, Subrepresentation.ext, range_inr
-/
lemma range_inr : (inr A ρ σ).range = (fst A ρ σ).ker :=
Subrepresentation.ext LinearMap.range_inr ..

/--
lemma `fst_comp_inl` / 引理 `fst_comp_inl`

English:
lemma fst_comp_inl
  statement: (fst A ρ σ).comp (inl A ρ σ) = id ρ
  proof: IntertwiningMap.ext LinearMap.fst_comp_inl ..

中文:
引理 fst_comp_inl
  结论: (fst A ρ σ).comp (inl A ρ σ) = id ρ
  证明: IntertwiningMap.ext LinearMap.fst_comp_inl ..
-/
@[simp] lemma fst_comp_inl : (fst A ρ σ).comp (inl A ρ σ) = id ρ :=
IntertwiningMap.ext LinearMap.fst_comp_inl ..

/--
lemma `snd_comp_inl` / 引理 `snd_comp_inl`

English:
lemma snd_comp_inl
  statement: (snd A ρ σ).comp (inl A ρ σ) = 0
  proof: IntertwiningMap.ext LinearMap.snd_comp_inl ..

中文:
引理 snd_comp_inl
  结论: (snd A ρ σ).comp (inl A ρ σ) = 0
  证明: IntertwiningMap.ext LinearMap.snd_comp_inl ..
-/
@[simp] lemma snd_comp_inl : (snd A ρ σ).comp (inl A ρ σ) = 0 :=
IntertwiningMap.ext LinearMap.snd_comp_inl ..

/--
lemma `fst_comp_inr` / 引理 `fst_comp_inr`

English:
lemma fst_comp_inr
  statement: (fst A ρ σ).comp (inr A ρ σ) = 0
  proof: IntertwiningMap.ext LinearMap.fst_comp_inr ..

中文:
引理 fst_comp_inr
  结论: (fst A ρ σ).comp (inr A ρ σ) = 0
  证明: IntertwiningMap.ext LinearMap.fst_comp_inr ..
-/
@[simp] lemma fst_comp_inr : (fst A ρ σ).comp (inr A ρ σ) = 0 :=
IntertwiningMap.ext LinearMap.fst_comp_inr ..

/--
lemma `snd_comp_inr` / 引理 `snd_comp_inr`

English:
lemma snd_comp_inr
  statement: (snd A ρ σ).comp (inr A ρ σ) = id σ
  proof: IntertwiningMap.ext LinearMap.snd_comp_inr ..

中文:
引理 snd_comp_inr
  结论: (snd A ρ σ).comp (inr A ρ σ) = id σ
  证明: IntertwiningMap.ext LinearMap.snd_comp_inr ..
-/
@[simp] lemma snd_comp_inr : (snd A ρ σ).comp (inr A ρ σ) = id σ :=
IntertwiningMap.ext LinearMap.snd_comp_inr ..

/--
lemma `coprod_inl_inr` / 引理 `coprod_inl_inr`

English:
lemma coprod_inl_inr
  statement: (inl A ρ σ).comp (fst A ρ σ) + (inr A ρ σ).comp (snd A ρ σ) =
  proof: IntertwiningMap.ext LinearMap.coprod_inl_inr

中文:
引理 coprod_inl_inr
  结论: (inl A ρ σ).comp (fst A ρ σ) + (inr A ρ σ).comp (snd A ρ σ) =
  证明: IntertwiningMap.ext LinearMap.coprod_inl_inr
-/
@[simp] lemma coprod_inl_inr : (inl A ρ σ).comp (fst A ρ σ) + (inr A ρ σ).comp (snd A ρ σ) =
.id _ := IntertwiningMap.ext LinearMap.coprod_inl_inr

end prod

end IntertwiningMap

/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: extends IntertwiningMap ρ σ, V ≃ₗ[A] W
  extends: IntertwiningMap ρ σ, V ≃ₗ[A] W
  axioms and operations (1):
    - mk' : :

中文:
结构 等价
  参数: extends 整数ertwining映射 ρ σ, V ≃ₗ[A] W
  继承: 整数ertwining映射 ρ σ, V ≃ₗ[A] W
  公理与运算 (1 个):
    - mk' : :
-/
structure Equiv extends IntertwiningMap ρ σ, V ≃ₗ[A] W where
  mk' ::

attribute [coe] Equiv.toIntertwiningMap

/-- Underlying linear isomorphism of an equivalence of representations. -/
add_decl_doc Equiv.toLinearEquiv

/-- The intertwining map underlying an equivalence of representations. -/
add_decl_doc Equiv.toIntertwiningMap

namespace Equiv

variable {ρ σ} (φ : Equiv ρ σ)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  body: e
  isIntertwining' := he

中文:
定义 mk
  签名: (e : V ≃ₗ[A] W) (he : 对任意 g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  定义体: e
  isIntertwining' := he
-/
def mk (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) : ρ.Equiv σ where
  __ := e
  isIntertwining' := he

/--
lemma `toLinearEquiv_mk'` / 引理 `toLinearEquiv_mk'`

English:
lemma toLinearEquiv_mk'
  given: {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  proof: rfl

中文:
引理 toLinearEquiv_mk'
  条件: {e : V ≃ₗ[A] W} (he : 对任意 g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  证明: rfl
-/
lemma toLinearEquiv_mk' {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toLinearEquiv = e := rfl

/--
lemma `toIntertwiningMap_mk'` / 引理 `toIntertwiningMap_mk'`

English:
lemma toIntertwiningMap_mk'
  given: (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  proof: rfl

@[simp]

中文:
引理 to整数ertwiningMap_mk'
  条件: (e : V ≃ₗ[A] W) (he : 对任意 g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  证明: rfl

@[simp]
-/
lemma toIntertwiningMap_mk' (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toIntertwiningMap = ⟨e.toLinearMap, he⟩ := rfl

@[simp]
/--
lemma `toLinearMap_mk'` / 引理 `toLinearMap_mk'`

English:
lemma toLinearMap_mk'
  given: (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  proof: rfl

中文:
引理 toLinearMap_mk'
  条件: (e : V ≃ₗ[A] W) (he : 对任意 g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  证明: rfl
-/
lemma toLinearMap_mk' (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toLinearMap = e.toLinearMap := rfl

/--
lemma `toLinearEquiv_injective` / 引理 `toLinearEquiv_injective`

English:
lemma toLinearEquiv_injective
  statement: Function.Injective (toLinearEquiv : (σ.Equiv ρ) -> _)
  proof: fun φ ψ h => by cases φ; cases ψ; simpa [IntertwiningMap.ext_iff] using h

中文:
引理 toLinearEquiv_injective
  结论: 函数.单射 (toLinearEquiv : (σ.等价 ρ) -> _)
  证明: fun φ ψ h => by cases φ; cases ψ; simpa [IntertwiningMap.ext_iff] using h

Depends on / 依赖: IntertwiningMap, IntertwiningMap.ext_iff, ext_iff
-/
lemma toLinearEquiv_injective : Function.Injective (toLinearEquiv : (σ.Equiv ρ) -> _) :=
  fun φ ψ h => by cases φ; cases ψ; simpa [IntertwiningMap.ext_iff] using h

/--
lemma `toLinearEquiv_inj` / 引理 `toLinearEquiv_inj`

English:
lemma toLinearEquiv_inj
  given: (φ ψ : σ.Equiv ρ)
  statement: φ.toLinearEquiv = ψ.toLinearEquiv ↔ φ = ψ
  proof: toLinearEquiv_injective.eq_iff

中文:
引理 toLinearEquiv_inj
  条件: (φ ψ : σ.等价 ρ)
  结论: φ.toLinearEquiv = ψ.toLinearEquiv ↔ φ = ψ
  证明: toLinearEquiv_injective.eq_iff

Depends on / 依赖: IsNontrivial, IsNontrivial.condition, condition, eq_iff, lt_or_lt_iff_ne, lt_or_lt_iff_ne.mpr, toLinearEquiv_injective, toLinearEquiv_injective.eq_iff, zero_lt_iff, zero_lt_iff.mpr
-/
lemma toLinearEquiv_inj (φ ψ : σ.Equiv ρ) : φ.toLinearEquiv = ψ.toLinearEquiv ↔ φ = ψ :=
  toLinearEquiv_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (Equiv ρ σ) V W
  body: φ.toLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by
    cases φ; cases ψ
    simp_all [IntertwiningMap.ext_iff]

中文:
实例 :
  签名: 等价状 (等价 ρ σ) V W
  定义体: φ.toLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by
    cases φ; cases ψ
    simp_all [IntertwiningMap.ext_iff]

Depends on / 依赖: toLinearEquiv
-/
instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by
    cases φ; cases ψ
    simp_all [IntertwiningMap.ext_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearEquivClass (σ.Equiv ρ) A W V
  body: f.map_add
  map_smulₛₗ f := f.map_smul

@[simp]

中文:
实例 :
  签名: LinearEquivClass (σ.等价 ρ) A W V
  定义体: f.map_add
  map_smulₛₗ f := f.map_smul

@[simp]

Depends on / 依赖: f.map_add, map_add
-/
instance : LinearEquivClass (σ.Equiv ρ) A W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

@[simp]
/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V)
  proof: rfl

@[ext]

中文:
引理 mk_apply
  条件: {e : V ≃ₗ[A] W} (he : 对任意 g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V)
  证明: rfl

@[ext]

Depends on / 依赖: isNontrivial_iff_isNontrivial
-/
lemma mk_apply {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ)
  statement: φ = ψ
  proof: by
  cases φ; cases ψ
  simpa using h

中文:
引理 ext
  条件: {φ ψ : 等价 ρ σ} (h : (φ : V -> W) = ψ)
  结论: φ = ψ
  证明: by
  cases φ; cases ψ
  simpa using h
-/
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : Equiv ρ ρ where
  body: LinearEquiv.refl _ _
  isIntertwining' g := by simp

中文:
定义 refl
  签名: : 等价 ρ ρ where
  定义体: LinearEquiv.refl _ _
  isIntertwining' g := by simp

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def refl : Equiv ρ ρ where
  __ := LinearEquiv.refl _ _
  isIntertwining' g := by simp

/--
lemma `toIntertwiningMap_refl` / 引理 `toIntertwiningMap_refl`

English:
lemma toIntertwiningMap_refl
  statement: (refl ρ).toIntertwiningMap = .id ρ
  proof: rfl

中文:
引理 to整数ertwiningMap_refl
  结论: (refl ρ).to整数ertwiningMap = .id ρ
  证明: rfl
-/
@[simp] lemma toIntertwiningMap_refl : (refl ρ).toIntertwiningMap = .id ρ := rfl

/--
lemma `toLinearMap_refl` / 引理 `toLinearMap_refl`

English:
lemma toLinearMap_refl
  statement: (refl ρ).toLinearMap = LinearMap.id
  proof: rfl

中文:
引理 toLinearMap_refl
  结论: (refl ρ).toLinearMap = 线性映射.id
  证明: rfl
-/
@[simp] lemma toLinearMap_refl : (refl ρ).toLinearMap = LinearMap.id := rfl

/--
lemma `refl_apply` / 引理 `refl_apply`

English:
lemma refl_apply
  given: (v : V)
  statement: refl ρ v = v
  proof: rfl

中文:
引理 refl_apply
  条件: (v : V)
  结论: refl ρ v = v
  证明: rfl
-/
@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl

/--
lemma `coe_toIntertwiningMap` / 引理 `coe_toIntertwiningMap`

English:
lemma coe_toIntertwiningMap
  statement: ⇑φ.toIntertwiningMap = φ
  proof: rfl

中文:
引理 coe_to整数ertwiningMap
  结论: ⇑φ.to整数ertwiningMap = φ
  证明: rfl
-/
@[simp] lemma coe_toIntertwiningMap : ⇑φ.toIntertwiningMap = φ := rfl

/--
lemma `coe_toLinearMap` / 引理 `coe_toLinearMap`

English:
lemma coe_toLinearMap
  statement: ⇑φ.toLinearMap = φ
  proof: rfl

中文:
引理 coe_toLinearMap
  结论: ⇑φ.toLinearMap = φ
  证明: rfl
-/
@[simp] lemma coe_toLinearMap : ⇑φ.toLinearMap = φ := rfl

/--
lemma `coe_invFun` / 引理 `coe_invFun`

English:
lemma coe_invFun
  statement: φ.invFun = φ.symm
  proof: rfl

中文:
引理 coe_invFun
  结论: φ.invFun = φ.symm
  证明: rfl
-/
lemma coe_invFun : φ.invFun = φ.symm := rfl

/--
theorem `toLinearEquiv_toLinearMap` / 定理 `toLinearEquiv_toLinearMap`

English:
theorem toLinearEquiv_toLinearMap
  proof: rfl

中文:
定理 toLinearEquiv_toLinearMap
  证明: rfl
-/
theorem toLinearEquiv_toLinearMap :
  φ.toLinearEquiv.toLinearMap = φ.toIntertwiningMap.toLinearMap := rfl

/--
theorem `toLinearEquiv_apply` / 定理 `toLinearEquiv_apply`

English:
theorem toLinearEquiv_apply
  given: (v : V)
  statement: φ.toLinearEquiv v = φ.toIntertwiningMap v
  proof: rfl

中文:
定理 toLinearEquiv_apply
  条件: (v : V)
  结论: φ.toLinearEquiv v = φ.to整数ertwiningMap v
  证明: rfl
-/
theorem toLinearEquiv_apply (v : V) : φ.toLinearEquiv v = φ.toIntertwiningMap v := rfl

open LinearMap in
/-- The equiv between representations are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (φ : Equiv ρ σ)
  body: φ.toLinearEquiv.symm
  isIntertwining' g := by
    rw [← cancel_left φ.toLinearEquiv.injective]; rw [← comp_assoc]; rw [← comp_assoc]; rw [φ.1.2 g]; rw [φ.comp_symm]; rw [comp_assoc]; rw [φ.comp_symm]; rw [id_comp]; rw [comp_id]

中文:
定义 symm
  签名: (φ : 等价 ρ σ)
  定义体: φ.toLinearEquiv.symm
  isIntertwining' g := by
    rw [← cancel_left φ.toLinearEquiv.injective]; rw [← comp_assoc]; rw [← comp_assoc]; rw [φ.1.2 g]; rw [φ.comp_symm]; rw [comp_assoc]; rw [φ.comp_symm]; rw [id_comp]; rw [comp_id]

Depends on / 依赖: toLinearEquiv, toLinearEquiv.symm
-/
def symm (φ : Equiv ρ σ) : Equiv σ ρ where
  __ := φ.toLinearEquiv.symm
  isIntertwining' g := by
    rw [← cancel_left φ.toLinearEquiv.injective]; rw [← comp_assoc]; rw [← comp_assoc]; rw [φ.1.2 g]; rw [φ.comp_symm]; rw [comp_assoc]; rw [φ.comp_symm]; rw [id_comp]; rw [comp_id]

open LinearMap in
/--
lemma `_root_.LinearEquiv.isIntertwining_symm_isIntertwining` / 引理 `_root_.LinearEquiv.isIntertwining_symm_isIntertwining`

English:
lemma _root_.LinearEquiv.isIntertwining_symm_isIntertwining
  statement: {e : V ≃ₗ[A] W}
  proof: by
.1 apply e.comp_toLinearMap_eq_iff _ _
  rw [← comp_assoc]; rw [← comp_assoc]; rw [he g]; rw [e.comp_symm]; rw [id_comp]; rw [comp_assoc]; rw [e.comp_symm]; rw [comp_id]

@[simp]

中文:
引理 _root_.线性等价.is整数ertwining_symm_is整数ertwining
  结论: {e : V ≃ₗ[A] W}
  证明: by
.1 apply e.comp_toLinearMap_eq_iff _ _
  rw [← comp_assoc]; rw [← comp_assoc]; rw [he g]; rw [e.comp_symm]; rw [id_comp]; rw [comp_assoc]; rw [e.comp_symm]; rw [comp_id]

@[simp]

Depends on / 依赖: comp_assoc, comp_id, comp_symm, comp_toLinearMap_eq_iff, e.comp_symm, e.comp_toLinearMap_eq_iff, id_comp
-/
lemma _root_.LinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃ₗ[A] W}
    (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (g : G) :
    e.symm ∘ₗ (σ g) = (ρ g) ∘ₗ e.symm := by
.1 apply e.comp_toLinearMap_eq_iff _ _
  rw [← comp_assoc]; rw [← comp_assoc]; rw [he g]; rw [e.comp_symm]; rw [id_comp]; rw [comp_assoc]; rw [e.comp_symm]; rw [comp_id]

@[simp]
/--
lemma `mk_symm` / 引理 `mk_symm`

English:
lemma mk_symm
  given: {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  proof: rfl

中文:
引理 mk_symm
  条件: {e : V ≃ₗ[A] W} (he : 对任意 g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
  证明: rfl
-/
lemma mk_symm {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl

/--
lemma `toLinearMap_symm` / 引理 `toLinearMap_symm`

English:
lemma toLinearMap_symm
  given: (φ : Equiv ρ σ)
  statement: (symm φ).toLinearMap = φ.toLinearEquiv.symm
  proof: rfl

中文:
引理 toLinearMap_symm
  条件: (φ : 等价 ρ σ)
  结论: (symm φ).toLinearMap = φ.toLinearEquiv.symm
  证明: rfl
-/
lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl

/--
lemma `coe_symm` / 引理 `coe_symm`

English:
lemma coe_symm
  given: (φ : Equiv ρ σ)
  statement: ⇑φ.toLinearEquiv.symm = φ.symm
  proof: rfl

中文:
引理 coe_symm
  条件: (φ : 等价 ρ σ)
  结论: ⇑φ.toLinearEquiv.symm = φ.symm
  证明: rfl
-/
lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

variable {τ}

open LinearMap in
/-- Composition of two `Equiv`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (φ : Equiv ρ σ) (ψ : Equiv σ τ)
  body: φ.toLinearEquiv.trans ψ.toLinearEquiv
  isIntertwining' g := by
    rw [LinearEquiv.coe_trans]; rw [comp_assoc]; rw [φ.1.2]; rw [← comp_assoc]; rw [ψ.1.2]; rw [comp_assoc]

@[simp]

中文:
定义 trans
  签名: (φ : 等价 ρ σ) (ψ : 等价 σ τ)
  定义体: φ.toLinearEquiv.trans ψ.toLinearEquiv
  isIntertwining' g := by
    rw [LinearEquiv.coe_trans]; rw [comp_assoc]; rw [φ.1.2]; rw [← comp_assoc]; rw [ψ.1.2]; rw [comp_assoc]

@[simp]

Depends on / 依赖: toLinearEquiv, toLinearEquiv.trans
-/
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ where
  __ := φ.toLinearEquiv.trans ψ.toLinearEquiv
  isIntertwining' g := by
    rw [LinearEquiv.coe_trans]; rw [comp_assoc]; rw [φ.1.2]; rw [← comp_assoc]; rw [ψ.1.2]; rw [comp_assoc]

@[simp]
/--
lemma `toIntertwiningMap_trans` / 引理 `toIntertwiningMap_trans`

English:
lemma toIntertwiningMap_trans
  given: (φ : Equiv ρ σ) (ψ : Equiv σ τ)
  proof: rfl

@[simp]

中文:
引理 to整数ertwiningMap_trans
  条件: (φ : 等价 ρ σ) (ψ : 等价 σ τ)
  证明: rfl

@[simp]
-/
lemma toIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toIntertwiningMap = ψ.toIntertwiningMap.comp φ.toIntertwiningMap := rfl

@[simp]
/--
lemma `toLinearMap_trans` / 引理 `toLinearMap_trans`

English:
lemma toLinearMap_trans
  given: (φ : Equiv ρ σ) (ψ : Equiv σ τ)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_trans
  条件: (φ : 等价 ρ σ) (ψ : 等价 σ τ)
  证明: rfl

@[simp]
-/
lemma toLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toLinearMap = ψ.toLinearMap ∘ₗ φ.toLinearMap := rfl

@[simp]
/--
lemma `trans_apply` / 引理 `trans_apply`

English:
lemma trans_apply
  given: (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V)
  proof: rfl

@[simp]

中文:
引理 trans_apply
  条件: (φ : 等价 ρ σ) (ψ : 等价 σ τ) (v : V)
  证明: rfl

@[simp]
-/
lemma trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) :
    trans φ ψ v = ψ (φ v) := rfl

@[simp]
/--
lemma `apply_symm_apply` / 引理 `apply_symm_apply`

English:
lemma apply_symm_apply
  given: (φ : Equiv ρ σ) (v : W)
  statement: φ (φ.symm v) = v
  proof: φ.right_inv v

@[simp]

中文:
引理 apply_symm_apply
  条件: (φ : 等价 ρ σ) (v : W)
  结论: φ (φ.symm v) = v
  证明: φ.right_inv v

@[simp]

Depends on / 依赖: right_inv
-/
lemma apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v := φ.right_inv v

@[simp]
/--
lemma `symm_apply_apply` / 引理 `symm_apply_apply`

English:
lemma symm_apply_apply
  given: (φ : Equiv ρ σ) (v : V)
  statement: φ.symm (φ v) = v
  proof: φ.left_inv v

@[simp]

中文:
引理 symm_apply_apply
  条件: (φ : 等价 ρ σ) (v : V)
  结论: φ.symm (φ v) = v
  证明: φ.left_inv v

@[simp]

Depends on / 依赖: left_inv
-/
lemma symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v := φ.left_inv v

@[simp]
/--
lemma `trans_symm` / 引理 `trans_symm`

English:
lemma trans_symm
  given: (φ : Equiv ρ σ)
  statement: φ.trans φ.symm = .refl ρ
  proof: by ext; simp

@[simp]

中文:
引理 trans_symm
  条件: (φ : 等价 ρ σ)
  结论: φ.trans φ.symm = .refl ρ
  证明: by ext; simp

@[simp]
-/
lemma trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ := by ext; simp

@[simp]
/--
lemma `symm_trans` / 引理 `symm_trans`

English:
lemma symm_trans
  given: (φ : Equiv ρ σ)
  statement: φ.symm.trans φ = .refl σ
  proof: by ext; simp

中文:
引理 symm_trans
  条件: (φ : 等价 ρ σ)
  结论: φ.symm.trans φ = .refl σ
  证明: by ext; simp
-/
lemma symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ := by ext; simp

end Equiv

end Monoid

end non_comm

variable {A G V W U : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V ->ₗ[A] W)

variable {ρ σ} in
/--
theorem `Equiv.conj_apply_self` / 定理 `Equiv.conj_apply_self`

English:
theorem Equiv.conj_apply_self
  given: (g : G) (φ : Equiv ρ σ)
  statement: φ.conj (ρ g) = σ g
  proof: by
  ext w
  have := (congr($(φ.symm.toIntertwiningMap.2 g) w)).symm
  simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply, LinearEquiv.conj_apply_apply,
    coe_symm, toLinearEquiv_apply, coe_toIntertwiningMap] at this ⊢
  simp [this]

中文:
定理 等价.conj_apply_self
  条件: (g : G) (φ : 等价 ρ σ)
  结论: φ.conj (ρ g) = σ g
  证明: by
  ext w
  have := (congr($(φ.symm.toIntertwiningMap.2 g) w)).symm
  simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply, LinearEquiv.conj_apply_apply,
    coe_symm, toLinearEquiv_apply, coe_toIntertwiningMap] at this ⊢
  simp [this]

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.conj_apply_apply, LinearMap, LinearMap.coe_comp, coe_comp, coe_symm, coe_toIntertwiningMap, coe_toLinearMap, comp_apply, conj_apply_apply, symm.toIntertwiningMap, toIntertwiningMap, toLinearEquiv_apply
-/
theorem Equiv.conj_apply_self (g : G) (φ : Equiv ρ σ) : φ.conj (ρ g) = σ g := by
  ext w
  have := (congr($(φ.symm.toIntertwiningMap.2 g) w)).symm
  simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply, LinearEquiv.conj_apply_apply,
    coe_symm, toLinearEquiv_apply, coe_toIntertwiningMap] at this ⊢
  simp [this]

section Monoid

namespace IntertwiningMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul A (IntertwiningMap ρ σ)
  body: ⟨fun a f => ⟨a • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

中文:
实例 :
  签名: 标量乘法 A (整数ertwining映射 ρ σ)
  定义体: ⟨fun a f => ⟨a • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.comp_smul, LinearMap.smul_comp, comp_smul, f.toLinearMap, smul_comp, toLinearMap
-/
instance : SMul A (IntertwiningMap ρ σ) :=
  ⟨fun a f => ⟨a • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (a : A) (f : IntertwiningMap ρ σ)
  proof: rfl

@[simp]

中文:
引理 coe_smul
  条件: (a : A) (f : 整数ertwining映射 ρ σ)
  证明: rfl

@[simp]
-/
@[simp] lemma coe_smul (a : A) (f : IntertwiningMap ρ σ) :
    ((a • f : IntertwiningMap ρ σ) : V -> W) = a • f := rfl

@[simp]
/--
lemma `toLinearMap_smul` / 引理 `toLinearMap_smul`

English:
lemma toLinearMap_smul
  given: (a : A) (f : IntertwiningMap ρ σ)
  proof: rfl

中文:
引理 toLinearMap_smul
  条件: (a : A) (f : 整数ertwining映射 ρ σ)
  证明: rfl
-/
lemma toLinearMap_smul (a : A) (f : IntertwiningMap ρ σ) :
    (a • f).toLinearMap = a • f.toLinearMap := rfl

/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (a : A) (f : IntertwiningMap ρ σ) (v : V)
  proof: rfl

中文:
引理 smul_apply
  条件: (a : A) (f : 整数ertwining映射 ρ σ) (v : V)
  证明: rfl
-/
lemma smul_apply (a : A) (f : IntertwiningMap ρ σ) (v : V) :
    (a • f) v = a • f v := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module A (IntertwiningMap ρ σ)
  body: fast_instance%
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

中文:
实例 :
  签名: 模 A (整数ertwining映射 ρ σ)
  定义体: fast_instance%
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.Injective.module, Injective, coeFnAddMonoidHom, coe_injective, coe_smul, fast_instance, module
-/
instance : Module A (IntertwiningMap ρ σ) :=
  fast_instance%
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equivLinearMapAsModule` / `equivLinearMapAsModule` 的定义

English:
definition equivLinearMapAsModule
  signature: :
  body: { toFun := f.toLinearMap
      map_add' := f.toLinearMap.map_add'
      map_smul' m v := by
        induction m using MonoidAlgebra.induction_linear with
          | zero => simp [f.toLinearMap.map_zero]
          | add x y hx hy => simp [add_smul, map_add, hx, hy]
          | single g a => simp [f.

中文:
定义 equivLinearMapAsModule
  签名: :
  定义体: { toFun := f.toLinearMap
      map_add' := f.toLinearMap.map_add'
      map_smul' m v := by
        induction m using MonoidAlgebra.induction_linear with
          | zero => simp [f.toLinearMap.map_zero]
          | add x y hx hy => simp [add_smul, map_add, hx, hy]
          | single g a => simp [f.

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.induction_linear, MonoidAlgebra.single, add_smul, f.isIntertwining, f.map_smul, f.toLinearMap, f.toLinearMap.map_add, f.toLinearMap.map_zero, induction_linear, invFun, isIntertwining, left_inv, map_add, map_smul, map_zero, single, toLinearMap
-/
def equivLinearMapAsModule :
    IntertwiningMap ρ σ ≃ₗ[A] ρ.asModule ->ₗ[A[G]] σ.asModule where
  toFun f :=
    { toFun := f.toLinearMap
      map_add' := f.toLinearMap.map_add'
      map_smul' m v := by
        induction m using MonoidAlgebra.induction_linear with
          | zero => simp [f.toLinearMap.map_zero]
          | add x y hx hy => simp [add_smul, map_add, hx, hy]
          | single g a => simp [f.isIntertwining]; rfl }
  invFun f :=
    { toLinearMap := { f with
        map_smul' a v := by simp }
      isIntertwining' g := by ext v; simpa using! f.map_smul' (MonoidAlgebra.single g 1) v }
  map_add' g₁ g₂ := by ext; simp
  map_smul' t g := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `llcomp` / `llcomp` 的定义

English:
definition llcomp
  signature: : IntertwiningMap σ τ ->ₗ[A] IntertwiningMap ρ σ ->ₗ[A] IntertwiningMap ρ τ where
  body: { toFun g := ((f.toLinearMap.comp g.toLinearMap).intertwiningMap_of_isIntertwiningMap ρ τ
      (by intro γ v; simp [f.isIntertwining, g.isIntertwining]))
      map_add' _ _ := by ext; simp [map_add, toLinearMap_apply]
      map_smul' _ _ := by ext; simp [toLinearMap_apply] }
  map_add' _ _ := by ex

中文:
定义 llcomp
  签名: : 整数ertwining映射 σ τ ->ₗ[A] 整数ertwining映射 ρ σ ->ₗ[A] 整数ertwining映射 ρ τ where
  定义体: { toFun g := ((f.toLinearMap.comp g.toLinearMap).intertwiningMap_of_isIntertwiningMap ρ τ
      (by intro γ v; simp [f.isIntertwining, g.isIntertwining]))
      map_add' _ _ := by ext; simp [map_add, toLinearMap_apply]
      map_smul' _ _ := by ext; simp [toLinearMap_apply] }
  map_add' _ _ := by ex

Depends on / 依赖: f.isIntertwining, f.toLinearMap.comp, g.isIntertwining, g.toLinearMap, intertwiningMap_of_isIntertwiningMap, isIntertwining, map_add, map_smul, toLinearMap, toLinearMap_apply
-/
def llcomp : IntertwiningMap σ τ ->ₗ[A] IntertwiningMap ρ σ ->ₗ[A] IntertwiningMap ρ τ where
  toFun f :=
    { toFun g := ((f.toLinearMap.comp g.toLinearMap).intertwiningMap_of_isIntertwiningMap ρ τ
      (by intro γ v; simp [f.isIntertwining, g.isIntertwining]))
      map_add' _ _ := by ext; simp [map_add, toLinearMap_apply]
      map_smul' _ _ := by ext; simp [toLinearMap_apply] }
  map_add' _ _ := by ext; simp [toLinearMap_apply]
  map_smul' _ _ := by ext; simp [toLinearMap_apply]

/--
lemma `comp_def` / 引理 `comp_def`

English:
lemma comp_def
  given: (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ)
  proof: rfl

中文:
引理 comp_def
  条件: (f : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ)
  证明: rfl
-/
lemma comp_def (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    comp f g = llcomp _ _ _ f g := rfl

/--
lemma `smul_comp` / 引理 `smul_comp`

English:
lemma smul_comp
  given: (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ)
  proof: by simp [comp_def]

中文:
引理 smul_comp
  条件: (a : A) (f : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ)
  证明: by simp [comp_def]

Depends on / 依赖: comp_def
-/
lemma smul_comp (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (a • f).comp g = a • comp f g := by simp [comp_def]

/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  given: (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ)
  proof: by simp [comp_def]

中文:
引理 comp_smul
  条件: (a : A) (f : 整数ertwining映射 σ τ) (g : 整数ertwining映射 ρ σ)
  证明: by simp [comp_def]

Depends on / 依赖: comp_def
-/
lemma comp_smul (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    comp f (a • g) = a • comp f g := by simp [comp_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (IntertwiningMap ρ ρ)
  body: comp

中文:
实例 :
  签名: 乘法 (整数ertwining映射 ρ ρ)
  定义体: comp
-/
instance : Mul (IntertwiningMap ρ ρ) where
  mul := comp

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (f g : IntertwiningMap ρ ρ)
  proof: rfl

中文:
引理 coe_mul
  条件: (f g : 整数ertwining映射 ρ ρ)
  证明: rfl
-/
@[simp] lemma coe_mul (f g : IntertwiningMap ρ ρ) :
    (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl

/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (f g : IntertwiningMap ρ ρ) (v : V)
  statement: (f * g) v = f (g v)
  proof: rfl

中文:
引理 mul_apply
  条件: (f g : 整数ertwining映射 ρ ρ) (v : V)
  结论: (f * g) v = f (g v)
  证明: rfl
-/
@[simp] lemma mul_apply (f g : IntertwiningMap ρ ρ) (v : V) : (f * g) v = f (g v) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (IntertwiningMap ρ ρ)
  body: ⟨id ρ⟩

中文:
实例 :
  签名: 幺 (整数ertwining映射 ρ ρ)
  定义体: ⟨id ρ⟩
-/
instance : One (IntertwiningMap ρ ρ) := ⟨id ρ⟩

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : IntertwiningMap ρ ρ) : V -> V) = (_root_.id : V -> V)
  proof: rfl

中文:
引理 coe_one
  结论: ((1 : 整数ertwining映射 ρ ρ) : V -> V) = (_root_.id : V -> V)
  证明: rfl
-/
@[simp] lemma coe_one : ((1 : IntertwiningMap ρ ρ) : V -> V) = (_root_.id : V -> V) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semigroup (IntertwiningMap ρ ρ)
  body: Function.Injective.semigroup (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) (coe_mul ρ)

中文:
实例 :
  签名: 半群 (整数ertwining映射 ρ ρ)
  定义体: Function.Injective.semigroup (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) (coe_mul ρ)

Depends on / 依赖: Function, Function.Injective.semigroup, Injective, IntertwiningMap, coe_mul, f.toLinearMap, semigroup, toLinearMap, toLinearMap_injective
-/
instance : Semigroup (IntertwiningMap ρ ρ) :=
  Function.Injective.semigroup (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) (coe_mul ρ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (IntertwiningMap ρ ρ) Nat
  body: ⟨fun f n => npowRecAuto n f⟩

中文:
实例 :
  签名: 幂 (整数ertwining映射 ρ ρ) 自然数
  定义体: ⟨fun f n => npowRecAuto n f⟩

Depends on / 依赖: npowRecAuto
-/
instance : Pow (IntertwiningMap ρ ρ) Nat := ⟨fun f n => npowRecAuto n f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (IntertwiningMap ρ ρ)
  body: Function.Injective.monoid (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl (fun _ _ => rfl)
    (fun f n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ, coe_mul, show f ^ (n + 1) = f ^ n * f from rfl, ih])

中文:
实例 :
  签名: 幺半群 (整数ertwining映射 ρ ρ)
  定义体: Function.Injective.monoid (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl (fun _ _ => rfl)
    (fun f n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ, coe_mul, show f ^ (n + 1) = f ^ n * f from rfl, ih])

Depends on / 依赖: Function, Function.Injective.monoid, Injective, IntertwiningMap, coe_mul, f.toLinearMap, monoid, pow_succ, toLinearMap, toLinearMap_injective
-/
instance : Monoid (IntertwiningMap ρ ρ) :=
  Function.Injective.monoid (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl (fun _ _ => rfl)
    (fun f n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ, coe_mul, show f ^ (n + 1) = f ^ n * f from rfl, ih])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (IntertwiningMap ρ ρ)
  body: n • (1 : IntertwiningMap ρ ρ)

中文:
实例 :
  签名: 自然数嵌入 (整数ertwining映射 ρ ρ)
  定义体: n • (1 : IntertwiningMap ρ ρ)

Depends on / 依赖: IntertwiningMap
-/
instance : NatCast (IntertwiningMap ρ ρ) where
  natCast n := n • (1 : IntertwiningMap ρ ρ)

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (IntertwiningMap ρ ρ)
  body: fast_instance%
  Function.Injective.semiring (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro f n
      induction n with
      | zero => rfl
      | succ n ih => simp [ih, pow_succ])
    (fun

中文:
实例 instSemiring
  签名: : 半环 (整数ertwining映射 ρ ρ)
  定义体: fast_instance%
  Function.Injective.semiring (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro f n
      induction n with
      | zero => rfl
      | succ n ih => simp [ih, pow_succ])
    (fun

Depends on / 依赖: Function, Function.Injective.semiring, Injective, IntertwiningMap, f.toLinearMap, fast_instance, pow_succ, semiring, toLinearMap, toLinearMap_injective
-/
instance instSemiring : Semiring (IntertwiningMap ρ ρ) :=
  fast_instance%
  Function.Injective.semiring (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro f n
      induction n with
      | zero => rfl
      | succ n ih => simp [ih, pow_succ])
    (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra A (IntertwiningMap ρ ρ)
  body: Algebra.ofModule (fun a f g => rfl) (fun a f g => by ext; simp)

中文:
实例 :
  签名: 代数 A (整数ertwining映射 ρ ρ)
  定义体: Algebra.ofModule (fun a f g => rfl) (fun a f g => by ext; simp)

Depends on / 依赖: Algebra, Algebra.ofModule, ofModule
-/
instance : Algebra A (IntertwiningMap ρ ρ) :=
  Algebra.ofModule (fun a f g => rfl) (fun a f g => by ext; simp)

/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (a : A)
  statement: algebraMap A (IntertwiningMap ρ ρ) a = a • 1
  proof: rfl

中文:
引理 algebraMap_apply
  条件: (a : A)
  结论: algebraMap A (整数ertwining映射 ρ ρ) a = a • 1
  证明: rfl
-/
@[simp] lemma algebraMap_apply (a : A) : algebraMap A (IntertwiningMap ρ ρ) a = a • 1 := rfl

/--
Definition of `equivAlgEnd` / `equivAlgEnd` 的定义

English:
definition equivAlgEnd
  signature: :
  body: AlgEquiv.ofLinearEquiv
    (equivLinearMapAsModule ρ ρ)
    rfl
    (by intro f g; rfl)

中文:
定义 equivAlgEnd
  签名: :
  定义体: AlgEquiv.ofLinearEquiv
    (equivLinearMapAsModule ρ ρ)
    rfl
    (by intro f g; rfl)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, equivLinearMapAsModule, ofLinearEquiv
-/
noncomputable def equivAlgEnd :
    IntertwiningMap ρ ρ ≃ₐ[A] Module.End A[G] ρ.asModule :=
  AlgEquiv.ofLinearEquiv
    (equivLinearMapAsModule ρ ρ)
    rfl
    (by intro f g; rfl)

/--
theorem `isIntertwiningMap_of_mem_center` / 定理 `isIntertwiningMap_of_mem_center`

English:
theorem isIntertwiningMap_of_mem_center
  given: (g : G) (hg : g in Submonoid.center G)
  proof: by
  rw [isIntertwiningMap_iff]
  intro g' v
  rw [Submonoid.mem_center_iff] at hg
  rw [← Module.End.mul_apply]; rw [← Module.End.mul_apply]; rw [← ρ.map_mul]; rw [← hg g']; rw [ρ.map_mul]

中文:
定理 is整数ertwiningMap_of_mem_center
  条件: (g : G) (hg : g in 子幺半群.center G)
  证明: by
  rw [isIntertwiningMap_iff]
  intro g' v
  rw [Submonoid.mem_center_iff] at hg
  rw [← Module.End.mul_apply]; rw [← Module.End.mul_apply]; rw [← ρ.map_mul]; rw [← hg g']; rw [ρ.map_mul]

Depends on / 依赖: Module, Module.End.mul_apply, Submonoid, Submonoid.mem_center_iff, isIntertwiningMap_iff, map_mul, mem_center_iff, mul_apply
-/
theorem isIntertwiningMap_of_mem_center (g : G) (hg : g in Submonoid.center G) :
    IsIntertwiningMap ρ ρ (ρ g) := by
  rw [isIntertwiningMap_iff]
  intro g' v
  rw [Submonoid.mem_center_iff] at hg
  rw [← Module.End.mul_apply]; rw [← Module.End.mul_apply]; rw [← ρ.map_mul]; rw [← hg g']; rw [ρ.map_mul]

/--
Definition of `centralMul` / `centralMul` 的定义

English:
definition centralMul
  signature: (g : G) (hg : g in Submonoid.center G)
  body: ρ g
isIntertwining' x := LinearMap.ext (isIntertwiningMap_of_mem_center ρ g hg).isIntertwining x

中文:
定义 centralMul
  签名: (g : G) (hg : g in 子幺半群.center G)
  定义体: ρ g
isIntertwining' x := LinearMap.ext (isIntertwiningMap_of_mem_center ρ g hg).isIntertwining x
-/
def centralMul (g : G) (hg : g in Submonoid.center G) : IntertwiningMap ρ ρ where
  toLinearMap := ρ g
isIntertwining' x := LinearMap.ext (isIntertwiningMap_of_mem_center ρ g hg).isIntertwining x

/--
Definition of `centralAlgebraMul` / `centralAlgebraMul` 的定义

English:
definition centralAlgebraMul
  signature: {z : A[G]} (hz : z in Submonoid.center A[G])
  body: ρ.asAlgebraHom z
  isIntertwining' _ := by simp_rw [← ρ.asAlgebraHom_of, ← Module.End.mul_eq_comp,
    ← map_mul, Submonoid.mem_center_iff.1 hz]

中文:
定义 centralAlgebraMul
  签名: {z : A[G]} (hz : z in 子幺半群.center A[G])
  定义体: ρ.asAlgebraHom z
  isIntertwining' _ := by simp_rw [← ρ.asAlgebraHom_of, ← Module.End.mul_eq_comp,
    ← map_mul, Submonoid.mem_center_iff.1 hz]

Depends on / 依赖: asAlgebraHom
-/
noncomputable def centralAlgebraMul {z : A[G]} (hz : z in Submonoid.center A[G]) :
    ρ.IntertwiningMap ρ where
  toLinearMap := ρ.asAlgebraHom z
  isIntertwining' _ := by simp_rw [← ρ.asAlgebraHom_of, ← Module.End.mul_eq_comp,
    ← map_mul, Submonoid.mem_center_iff.1 hz]

/--
lemma `centralAlgebraMul_apply` / 引理 `centralAlgebraMul_apply`

English:
lemma centralAlgebraMul_apply
  given: {z : A[G]} (hz : z in Submonoid.center A[G]) (v : V)
  proof: rfl

中文:
引理 centralAlgebraMul_apply
  条件: {z : A[G]} (hz : z in 子幺半群.center A[G]) (v : V)
  证明: rfl
-/
@[simp] lemma centralAlgebraMul_apply {z : A[G]} (hz : z in Submonoid.center A[G]) (v : V) :
    centralAlgebraMul ρ hz v = ρ.asAlgebraHom z v := rfl

/--
Definition of `centralAlgebraMulHom` / `centralAlgebraMulHom` 的定义

English:
definition centralAlgebraMulHom
  signature: : Submonoid.center A[G] ->* ρ.IntertwiningMap ρ where
  body: centralAlgebraMul _ z.2
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

中文:
定义 centralAlgebraMulHom
  签名: : 子幺半群.center A[G] ->* ρ.整数ertwining映射 ρ where
  定义体: centralAlgebraMul _ z.2
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
-/
@[simps] noncomputable def centralAlgebraMulHom : Submonoid.center A[G] ->* ρ.IntertwiningMap ρ where
  toFun z := centralAlgebraMul _ z.2
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/--
Definition of `toLinearMapl` / `toLinearMapl` 的定义

English:
definition toLinearMapl
  signature: : IntertwiningMap ρ σ ->ₗ[A] V ->ₗ[A] W where
  body: toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 toLinearMapl
  签名: : 整数ertwining映射 ρ σ ->ₗ[A] V ->ₗ[A] W where
  定义体: toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
@[simps] def toLinearMapl : IntertwiningMap ρ σ ->ₗ[A] V ->ₗ[A] W where
  toFun := toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A G V W : Type*} [CommRing A] [Monoid G] [AddCommGroup V] [AddCommGroup W]
  [Module A V] [Module A W] (ρ : Representation A G V) (σ : Representation A G W) in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: A V] [IsNoetherian A W] :
  body: .of_injective (toLinearMapl (ρ := ρ) (σ := σ)) (toLinearMap_injective ρ σ)

中文:
实例 [模.有限
  签名: A V] [是Noether A W] :
  定义体: .of_injective (toLinearMapl (ρ := ρ) (σ := σ)) (toLinearMap_injective ρ σ)

Depends on / 依赖: of_injective, toLinearMap_injective, toLinearMapl
-/
instance [Module.Finite A V] [IsNoetherian A W] :
    Module.Finite A (IntertwiningMap ρ σ) :=
  .of_injective (toLinearMapl (ρ := ρ) (σ := σ)) (toLinearMap_injective ρ σ)

variable {ρ σ} in
/-- A bijective intertwining map is an equivalence of representations. -/
noncomputable
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : IntertwiningMap ρ σ) (hf : Function.Bijective f)
  body: f.isIntertwining'
  toLinearEquiv := LinearEquiv.ofBijective f.toLinearMap hf

@[simp]

中文:
定义 ofBijective
  签名: (f : 整数ertwining映射 ρ σ) (hf : 函数.双射 f)
  定义体: f.isIntertwining'
  toLinearEquiv := LinearEquiv.ofBijective f.toLinearMap hf

@[simp]

Depends on / 依赖: f.isIntertwining, isIntertwining
-/
def ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) :
    Equiv ρ σ where
  isIntertwining' := f.isIntertwining'
  toLinearEquiv := LinearEquiv.ofBijective f.toLinearMap hf

@[simp]
/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  given: (f : IntertwiningMap ρ σ) (hf : Function.Bijective f)
  proof: rfl

中文:
定理 coe_ofBijective
  条件: (f : 整数ertwining映射 ρ σ) (hf : 函数.双射 f)
  证明: rfl
-/
theorem coe_ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) :
    ⇑(f.ofBijective hf) = ⇑f := rfl

variable {P : Type*} [AddCommMonoid P] [Module A P] {π : Representation A G P}

variable {ρ σ τ}

/--
Definition of `tensor` / `tensor` 的定义

English:
definition tensor
  signature: (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π)
  body: TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := by
    rw [tprod_apply]; rw [← TensorProduct.map_comp]; rw [f.2]; rw [g.2]; rw [TensorProduct.map_comp]; rw [tprod_apply]

@[simp]

中文:
定义 tensor
  签名: (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 τ π)
  定义体: TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := by
    rw [tprod_apply]; rw [← TensorProduct.map_comp]; rw [f.2]; rw [g.2]; rw [TensorProduct.map_comp]; rw [tprod_apply]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.map, f.toLinearMap, g.toLinearMap, toLinearMap
-/
def tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (tprod ρ τ).IntertwiningMap (tprod σ π) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := by
    rw [tprod_apply]; rw [← TensorProduct.map_comp]; rw [f.2]; rw [g.2]; rw [TensorProduct.map_comp]; rw [tprod_apply]

@[simp]
/--
lemma `toLinearMap_tensor` / 引理 `toLinearMap_tensor`

English:
lemma toLinearMap_tensor
  given: (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_tensor
  条件: (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 τ π)
  证明: rfl

@[simp]
-/
lemma toLinearMap_tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (f.tensor g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

@[simp]
/--
lemma `tensor_add_left` / 引理 `tensor_add_left`

English:
lemma tensor_add_left
  given: (f₁ f₂ : IntertwiningMap ρ σ) (g : IntertwiningMap τ π)
  proof: by ext; simp [TensorProduct.add_tmul]

@[simp]

中文:
引理 tensor_add_left
  条件: (f₁ f₂ : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 τ π)
  证明: by ext; simp [TensorProduct.add_tmul]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.add_tmul, add_tmul
-/
lemma tensor_add_left (f₁ f₂ : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (f₁ + f₂).tensor g = f₁.tensor g + f₂.tensor g := by ext; simp [TensorProduct.add_tmul]

@[simp]
/--
lemma `tensor_add_right` / 引理 `tensor_add_right`

English:
lemma tensor_add_right
  given: (f : IntertwiningMap ρ σ) (g₁ g₂ : IntertwiningMap τ π)
  proof: by ext; simp [TensorProduct.tmul_add]

@[simp]

中文:
引理 tensor_add_right
  条件: (f : 整数ertwining映射 ρ σ) (g₁ g₂ : 整数ertwining映射 τ π)
  证明: by ext; simp [TensorProduct.tmul_add]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.tmul_add, tmul_add
-/
lemma tensor_add_right (f : IntertwiningMap ρ σ) (g₁ g₂ : IntertwiningMap τ π) :
    f.tensor (g₁ + g₂) = f.tensor g₁ + f.tensor g₂ := by ext; simp [TensorProduct.tmul_add]

@[simp]
/--
lemma `tensor_smul_left` / 引理 `tensor_smul_left`

English:
lemma tensor_smul_left
  given: (a : A) (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π)
  proof: by ext; simp [TensorProduct.smul_tmul]

@[simp]

中文:
引理 tensor_smul_left
  条件: (a : A) (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 τ π)
  证明: by ext; simp [TensorProduct.smul_tmul]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.smul_tmul, smul_tmul
-/
lemma tensor_smul_left (a : A) (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (a • f).tensor g = a • (f.tensor g) := by ext; simp [TensorProduct.smul_tmul]

@[simp]
/--
lemma `tensor_smul_right` / 引理 `tensor_smul_right`

English:
lemma tensor_smul_right
  given: (f : IntertwiningMap ρ σ) (a : A) (g : IntertwiningMap τ π)
  proof: by ext; simp [TensorProduct.tmul_smul]

@[simp]

中文:
引理 tensor_smul_right
  条件: (f : 整数ertwining映射 ρ σ) (a : A) (g : 整数ertwining映射 τ π)
  证明: by ext; simp [TensorProduct.tmul_smul]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.tmul_smul, tmul_smul
-/
lemma tensor_smul_right (f : IntertwiningMap ρ σ) (a : A) (g : IntertwiningMap τ π) :
    f.tensor (a • g) = a • (f.tensor g) := by ext; simp [TensorProduct.tmul_smul]

@[simp]
/--
lemma `tensor_apply` / 引理 `tensor_apply`

English:
lemma tensor_apply
  given: (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) (v : V) (w : U)
  proof: rfl

中文:
引理 tensor_apply
  条件: (f : 整数ertwining映射 ρ σ) (g : 整数ertwining映射 τ π) (v : V) (w : U)
  证明: rfl
-/
lemma tensor_apply (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) (v : V) (w : U) :
    f.tensor g (v otimesₜ w) = f v otimesₜ g w := rfl

variable (ρ) in
/--
Definition of `lTensor` / `lTensor` 的定义

English:
definition lTensor
  signature: (f : IntertwiningMap σ τ)
  body: tensor (id ρ) f

@[simp]

中文:
定义 lTensor
  签名: (f : 整数ertwining映射 σ τ)
  定义体: tensor (id ρ) f

@[simp]

Depends on / 依赖: tensor
-/
def lTensor (f : IntertwiningMap σ τ) :
    (tprod ρ σ).IntertwiningMap (tprod ρ τ) := tensor (id ρ) f

@[simp]
/--
lemma `toLinearMap_lTensor` / 引理 `toLinearMap_lTensor`

English:
lemma toLinearMap_lTensor
  given: (f : IntertwiningMap ρ σ)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_lTensor
  条件: (f : 整数ertwining映射 ρ σ)
  证明: rfl

@[simp]
-/
lemma toLinearMap_lTensor (f : IntertwiningMap ρ σ) :
    (f.lTensor τ).toLinearMap = f.toLinearMap.lTensor U := rfl

@[simp]
/--
lemma `lTensor_apply` / 引理 `lTensor_apply`

English:
lemma lTensor_apply
  given: (f : IntertwiningMap σ τ) (v : V) (w : W)
  proof: rfl

@[simp]

中文:
引理 lTensor_apply
  条件: (f : 整数ertwining映射 σ τ) (v : V) (w : W)
  证明: rfl

@[simp]
-/
lemma lTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) :
    f.lTensor ρ (v otimesₜ w) = v otimesₜ f w := rfl

@[simp]
/--
lemma `lTensor_id` / 引理 `lTensor_id`

English:
lemma lTensor_id
  statement: lTensor ρ (id σ) = id (tprod ρ σ)
  proof: by ext; simp

@[simp]

中文:
引理 lTensor_id
  结论: lTensor ρ (id σ) = id (tprod ρ σ)
  证明: by ext; simp

@[simp]
-/
lemma lTensor_id : lTensor ρ (id σ) = id (tprod ρ σ) := by ext; simp

@[simp]
/--
lemma `lTensor_zero` / 引理 `lTensor_zero`

English:
lemma lTensor_zero
  statement: lTensor ρ (0 : IntertwiningMap σ τ) = 0
  proof: by ext; simp

@[simp]

中文:
引理 lTensor_zero
  结论: lTensor ρ (0 : 整数ertwining映射 σ τ) = 0
  证明: by ext; simp

@[simp]
-/
lemma lTensor_zero : lTensor ρ (0 : IntertwiningMap σ τ) = 0 := by ext; simp

@[simp]
/--
lemma `lTensor_add` / 引理 `lTensor_add`

English:
lemma lTensor_add
  given: (f₁ f₂ : IntertwiningMap σ τ)
  proof: tensor_add_right _ _ _

@[simp]

中文:
引理 lTensor_add
  条件: (f₁ f₂ : 整数ertwining映射 σ τ)
  证明: tensor_add_right _ _ _

@[simp]

Depends on / 依赖: tensor_add_right
-/
lemma lTensor_add (f₁ f₂ : IntertwiningMap σ τ) :
    lTensor ρ (f₁ + f₂) = lTensor ρ f₁ + lTensor ρ f₂ := tensor_add_right _ _ _

@[simp]
/--
lemma `lTensor_smul` / 引理 `lTensor_smul`

English:
lemma lTensor_smul
  given: (a : A) (f : IntertwiningMap σ τ)
  proof: tensor_smul_right _ _ _

中文:
引理 lTensor_smul
  条件: (a : A) (f : 整数ertwining映射 σ τ)
  证明: tensor_smul_right _ _ _

Depends on / 依赖: tensor_smul_right
-/
lemma lTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    lTensor ρ (a • f) = a • lTensor ρ f := tensor_smul_right _ _ _

variable (ρ) in
/--
Definition of `rTensor` / `rTensor` 的定义

English:
definition rTensor
  signature: (f : IntertwiningMap σ τ)
  body: tensor f (id ρ)

@[simp]

中文:
定义 rTensor
  签名: (f : 整数ertwining映射 σ τ)
  定义体: tensor f (id ρ)

@[simp]

Depends on / 依赖: tensor
-/
def rTensor (f : IntertwiningMap σ τ) :
    (tprod σ ρ).IntertwiningMap (tprod τ ρ) := tensor f (id ρ)

@[simp]
/--
lemma `toLinearMap_rTensor` / 引理 `toLinearMap_rTensor`

English:
lemma toLinearMap_rTensor
  given: (f : IntertwiningMap σ τ)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_rTensor
  条件: (f : 整数ertwining映射 σ τ)
  证明: rfl

@[simp]
-/
lemma toLinearMap_rTensor (f : IntertwiningMap σ τ) :
    (f.rTensor ρ).toLinearMap = f.toLinearMap.rTensor V := rfl

@[simp]
/--
lemma `rTensor_apply` / 引理 `rTensor_apply`

English:
lemma rTensor_apply
  given: (f : IntertwiningMap σ τ) (v : V) (w : W)
  proof: rfl

@[simp]

中文:
引理 rTensor_apply
  条件: (f : 整数ertwining映射 σ τ) (v : V) (w : W)
  证明: rfl

@[simp]
-/
lemma rTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) :
    f.rTensor ρ (w otimesₜ v) = f w otimesₜ v := rfl

@[simp]
/--
lemma `rTensor_id` / 引理 `rTensor_id`

English:
lemma rTensor_id
  statement: rTensor ρ (id σ) = id (tprod σ ρ)
  proof: by ext; simp

@[simp]

中文:
引理 rTensor_id
  结论: rTensor ρ (id σ) = id (tprod σ ρ)
  证明: by ext; simp

@[simp]
-/
lemma rTensor_id : rTensor ρ (id σ) = id (tprod σ ρ) := by ext; simp

@[simp]
/--
lemma `rTensor_zero` / 引理 `rTensor_zero`

English:
lemma rTensor_zero
  statement: rTensor ρ (0 : IntertwiningMap σ τ) = 0
  proof: by ext; simp

@[simp]

中文:
引理 rTensor_zero
  结论: rTensor ρ (0 : 整数ertwining映射 σ τ) = 0
  证明: by ext; simp

@[simp]
-/
lemma rTensor_zero : rTensor ρ (0 : IntertwiningMap σ τ) = 0 := by ext; simp

@[simp]
/--
lemma `rTensor_add` / 引理 `rTensor_add`

English:
lemma rTensor_add
  given: (f₁ f₂ : IntertwiningMap σ τ)
  proof: tensor_add_left _ _ _

@[simp]

中文:
引理 rTensor_add
  条件: (f₁ f₂ : 整数ertwining映射 σ τ)
  证明: tensor_add_left _ _ _

@[simp]

Depends on / 依赖: tensor_add_left
-/
lemma rTensor_add (f₁ f₂ : IntertwiningMap σ τ) :
    rTensor ρ (f₁ + f₂) = rTensor ρ f₁ + rTensor ρ f₂ := tensor_add_left _ _ _

@[simp]
/--
lemma `rTensor_smul` / 引理 `rTensor_smul`

English:
lemma rTensor_smul
  given: (a : A) (f : IntertwiningMap σ τ)
  proof: tensor_smul_left _ _ _

中文:
引理 rTensor_smul
  条件: (a : A) (f : 整数ertwining映射 σ τ)
  证明: tensor_smul_left _ _ _

Depends on / 依赖: tensor_smul_left
-/
lemma rTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    rTensor ρ (a • f) = a • rTensor ρ f := tensor_smul_left _ _ _

variable {Q : Type*} [AddCommMonoid Q] [Module A Q] {υ : Representation A G Q}

/--
lemma `rTensor_comp_lTensor` / 引理 `rTensor_comp_lTensor`

English:
lemma rTensor_comp_lTensor
  given: (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ)
  proof: by ext; simp

中文:
引理 rTensor_comp_lTensor
  条件: (f : ρ.整数ertwining映射 τ) (g : σ.整数ertwining映射 υ)
  证明: by ext; simp
-/
lemma rTensor_comp_lTensor (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
    (f.rTensor υ).comp (g.lTensor ρ) = f.tensor g := by ext; simp

/--
lemma `lTensor_comp_rTensor` / 引理 `lTensor_comp_rTensor`

English:
lemma lTensor_comp_rTensor
  given: (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ)
  proof: by ext; simp

中文:
引理 lTensor_comp_rTensor
  条件: (f : ρ.整数ertwining映射 τ) (g : σ.整数ertwining映射 υ)
  证明: by ext; simp
-/
lemma lTensor_comp_rTensor (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
    (g.lTensor τ).comp (f.rTensor σ) = f.tensor g := by ext; simp

end IntertwiningMap

namespace TensorProduct

noncomputable section

/--
Definition of `comm` / `comm` 的定义

English:
definition comm
  signature: : (tprod ρ σ).Equiv (tprod σ ρ)
  body: .mk (_root_.TensorProduct.comm A V W) fun g => by ext; simp

@[simp]

中文:
定义 comm
  签名: : (tprod ρ σ).等价 (tprod σ ρ)
  定义体: .mk (_root_.TensorProduct.comm A V W) fun g => by ext; simp

@[simp]

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.comm
-/
def comm : (tprod ρ σ).Equiv (tprod σ ρ) :=
.mk (_root_.TensorProduct.comm A V W) fun g => by ext; simp

@[simp]
/--
lemma `toLinearMap_comm` / 引理 `toLinearMap_comm`

English:
lemma toLinearMap_comm
  statement: (comm ρ σ).toLinearMap = _root_.TensorProduct.comm A V W
  proof: rfl

@[simp]

中文:
引理 toLinearMap_comm
  结论: (comm ρ σ).toLinearMap = _root_.张量积.comm A V W
  证明: rfl

@[simp]
-/
lemma toLinearMap_comm : (comm ρ σ).toLinearMap = _root_.TensorProduct.comm A V W := rfl

@[simp]
/--
lemma `comm_apply` / 引理 `comm_apply`

English:
lemma comm_apply
  given: (v : V) (w : W)
  statement: comm ρ σ (v otimesₜ w) = w otimesₜ v
  proof: rfl

中文:
引理 comm_apply
  条件: (v : V) (w : W)
  结论: comm ρ σ (v otimesₜ w) = w otimesₜ v
  证明: rfl
-/
lemma comm_apply (v : V) (w : W) : comm ρ σ (v otimesₜ w) = w otimesₜ v := rfl

/--
lemma `comm_comp_lTensor` / 引理 `comm_comp_lTensor`

English:
lemma comm_comp_lTensor
  given: (f : IntertwiningMap σ τ)
  proof: by ext; simp

中文:
引理 comm_comp_lTensor
  条件: (f : 整数ertwining映射 σ τ)
  证明: by ext; simp
-/
lemma comm_comp_lTensor (f : IntertwiningMap σ τ) :
    (comm ρ τ).comp (f.lTensor ρ) = (f.rTensor ρ).comp (comm ρ σ).toIntertwiningMap := by ext; simp

/--
lemma `comm_comp_rTensor` / 引理 `comm_comp_rTensor`

English:
lemma comm_comp_rTensor
  given: (f : IntertwiningMap σ τ)
  proof: by ext; simp

中文:
引理 comm_comp_rTensor
  条件: (f : 整数ertwining映射 σ τ)
  证明: by ext; simp
-/
lemma comm_comp_rTensor (f : IntertwiningMap σ τ) :
    (comm τ ρ).comp (f.rTensor ρ) = (f.lTensor ρ).comp (comm σ ρ).toIntertwiningMap := by ext; simp

/--
lemma `comm_symm` / 引理 `comm_symm`

English:
lemma comm_symm
  statement: (comm σ ρ).symm = comm ρ σ
  proof: by rfl

中文:
引理 comm_symm
  结论: (comm σ ρ).symm = comm ρ σ
  证明: by rfl
-/
lemma comm_symm : (comm σ ρ).symm = comm ρ σ := by rfl

/--
Definition of `assoc` / `assoc` 的定义

English:
definition assoc
  signature: : (tprod (tprod ρ σ) τ).Equiv (tprod ρ (tprod σ τ))
  body: .mk (_root_.TensorProduct.assoc A V W U) fun g => by ext; simp

@[simp]

中文:
定义 assoc
  签名: : (tprod (tprod ρ σ) τ).等价 (tprod ρ (tprod σ τ))
  定义体: .mk (_root_.TensorProduct.assoc A V W U) fun g => by ext; simp

@[simp]

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.assoc
-/
def assoc : (tprod (tprod ρ σ) τ).Equiv (tprod ρ (tprod σ τ)) :=
.mk (_root_.TensorProduct.assoc A V W U) fun g => by ext; simp

@[simp]
/--
lemma `toLinearMap_assoc` / 引理 `toLinearMap_assoc`

English:
lemma toLinearMap_assoc
  statement: (assoc ρ σ τ).toLinearMap = _root_.TensorProduct.assoc A V W U
  proof: rfl

@[simp]

中文:
引理 toLinearMap_assoc
  结论: (assoc ρ σ τ).toLinearMap = _root_.张量积.assoc A V W U
  证明: rfl

@[simp]
-/
lemma toLinearMap_assoc : (assoc ρ σ τ).toLinearMap = _root_.TensorProduct.assoc A V W U := rfl

@[simp]
/--
lemma `assoc_symm_toLinearMap` / 引理 `assoc_symm_toLinearMap`

English:
lemma assoc_symm_toLinearMap
  statement: (assoc ρ σ τ).symm.toLinearMap =
  proof: rfl

@[simp]

中文:
引理 assoc_symm_toLinearMap
  结论: (assoc ρ σ τ).symm.toLinearMap =
  证明: rfl

@[simp]
-/
lemma assoc_symm_toLinearMap : (assoc ρ σ τ).symm.toLinearMap =
  (_root_.TensorProduct.assoc A V W U).symm := rfl

@[simp]
/--
lemma `assoc_apply` / 引理 `assoc_apply`

English:
lemma assoc_apply
  given: (v : V) (w : W) (u : U)
  statement: assoc ρ σ τ ((v otimesₜ w) otimesₜ u) = v otimesₜ (w otimesₜ u)
  proof: rfl

中文:
引理 assoc_apply
  条件: (v : V) (w : W) (u : U)
  结论: assoc ρ σ τ ((v otimesₜ w) otimesₜ u) = v otimesₜ (w otimesₜ u)
  证明: rfl
-/
lemma assoc_apply (v : V) (w : W) (u : U) : assoc ρ σ τ ((v otimesₜ w) otimesₜ u) = v otimesₜ (w otimesₜ u) := rfl

variable (A) in
/--
Definition of `rid` / `rid` 的定义

English:
definition rid
  signature: : (σ.tprod (trivial A G A)).Equiv σ
  body: .mk (_root_.TensorProduct.rid A W) fun g => by ext; simp

@[simp]

中文:
定义 rid
  签名: : (σ.tprod (trivial A G A)).等价 σ
  定义体: .mk (_root_.TensorProduct.rid A W) fun g => by ext; simp

@[simp]

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.rid
-/
def rid : (σ.tprod (trivial A G A)).Equiv σ :=
.mk (_root_.TensorProduct.rid A W) fun g => by ext; simp

@[simp]
/--
lemma `toLinearMap_rid` / 引理 `toLinearMap_rid`

English:
lemma toLinearMap_rid
  statement: (rid A σ).toLinearMap = _root_.TensorProduct.rid A W
  proof: rfl

@[simp]

中文:
引理 toLinearMap_rid
  结论: (rid A σ).toLinearMap = _root_.张量积.rid A W
  证明: rfl

@[simp]
-/
lemma toLinearMap_rid : (rid A σ).toLinearMap = _root_.TensorProduct.rid A W := rfl

@[simp]
/--
lemma `rid_apply` / 引理 `rid_apply`

English:
lemma rid_apply
  given: (w : W) (a : A)
  statement: rid A σ (w otimesₜ a) = a • w
  proof: rfl

@[simp]

中文:
引理 rid_apply
  条件: (w : W) (a : A)
  结论: rid A σ (w otimesₜ a) = a • w
  证明: rfl

@[simp]
-/
lemma rid_apply (w : W) (a : A) : rid A σ (w otimesₜ a) = a • w := rfl

@[simp]
/--
lemma `rid_symm_apply` / 引理 `rid_symm_apply`

English:
lemma rid_symm_apply
  given: (w : W)
  statement: (rid A σ).symm w = w otimesₜ 1
  proof: rfl

中文:
引理 rid_symm_apply
  条件: (w : W)
  结论: (rid A σ).symm w = w otimesₜ 1
  证明: rfl
-/
lemma rid_symm_apply (w : W) : (rid A σ).symm w = w otimesₜ 1 := rfl

variable (A) in
/--
Definition of `lid` / `lid` 的定义

English:
definition lid
  signature: : ((trivial A G A).tprod σ).Equiv σ
  body: .mk (_root_.TensorProduct.lid A W) fun g => by ext; simp

@[simp]

中文:
定义 lid
  签名: : ((trivial A G A).tprod σ).等价 σ
  定义体: .mk (_root_.TensorProduct.lid A W) fun g => by ext; simp

@[simp]

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.lid
-/
def lid : ((trivial A G A).tprod σ).Equiv σ :=
.mk (_root_.TensorProduct.lid A W) fun g => by ext; simp

@[simp]
/--
lemma `toLinearMap_lid` / 引理 `toLinearMap_lid`

English:
lemma toLinearMap_lid
  statement: (lid A σ).toLinearMap = _root_.TensorProduct.lid A W
  proof: rfl

@[simp]

中文:
引理 toLinearMap_lid
  结论: (lid A σ).toLinearMap = _root_.张量积.lid A W
  证明: rfl

@[simp]
-/
lemma toLinearMap_lid : (lid A σ).toLinearMap = _root_.TensorProduct.lid A W := rfl

@[simp]
/--
lemma `lid_apply` / 引理 `lid_apply`

English:
lemma lid_apply
  given: (a : A) (w : W)
  statement: lid A σ (a otimesₜ w) = a • w
  proof: rfl

@[simp]

中文:
引理 lid_apply
  条件: (a : A) (w : W)
  结论: lid A σ (a otimesₜ w) = a • w
  证明: rfl

@[simp]
-/
lemma lid_apply (a : A) (w : W) : lid A σ (a otimesₜ w) = a • w := rfl

@[simp]
/--
lemma `lid_symm_apply` / 引理 `lid_symm_apply`

English:
lemma lid_symm_apply
  given: (w : W)
  statement: (lid A σ).symm w = 1 otimesₜ w
  proof: rfl

中文:
引理 lid_symm_apply
  条件: (w : W)
  结论: (lid A σ).symm w = 1 otimesₜ w
  证明: rfl
-/
lemma lid_symm_apply (w : W) : (lid A σ).symm w = 1 otimesₜ w := rfl

end

end TensorProduct

end Monoid

namespace Equiv

section Group

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)

/--
Definition of `dualTensorHom` / `dualTensorHom` 的定义

English:
definition dualTensorHom
  signature: : Equiv (tprod ρ.dual σ) (linHom ρ σ) where
  body: dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]

中文:
定义 dualTensorHom
  签名: : 等价 (tprod ρ.dual σ) (linHom ρ σ) where
  定义体: dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]
-/
@[simps!] noncomputable def dualTensorHom : Equiv (tprod ρ.dual σ) (linHom ρ σ) where
  toLinearEquiv := dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]

end Group

end Equiv

end Representation
