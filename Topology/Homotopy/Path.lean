/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.Convex.Basic

/-!
# Homotopy between paths

In this file, we define a `Homotopy` between two `Path`s. In addition, we define a relation
`Homotopic` on `Path`s, and prove that it is an equivalence relation.

## Definitions

* `Path.Homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `Path.Homotopy.refl p` is the constant homotopy between `p` and itself
* `Path.Homotopy.symm F` is the `Path.Homotopy p₁ p₀` defined by reversing the homotopy
* `Path.Homotopy.trans F G`, where `F : Path.Homotopy p₀ p₁`, `G : Path.Homotopy p₁ p₂` is the
  `Path.Homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `Path.Homotopy.hcomp F G`, where `F : Path.Homotopy p₀ q₀` and `G : Path.Homotopy p₁ q₁` is
  a `Path.Homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `Path.Homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `Path.Homotopic.setoid x₀ x₁` is the setoid on `Path`s from `Path.Homotopic`
* `Path.Homotopic.Quotient x₀ x₁` is the quotient type from `Path x₀ x₀` by `Path.Homotopic.setoid`

-/

@[expose] public section


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ x₂ x₃ : X}

noncomputable section

open unitInterval

namespace Path

/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
abbreviation Homotopy
  signature: (p₀ p₁ : Path x₀ x₁)
  body: ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

中文:
缩写 Homotopy
  签名: (p₀ p₁ : Path x₀ x₁)
  定义体: ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel, HomotopyRel, toContinuousMap
-/
abbrev Homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

namespace Homotopy

section

variable {p₀ p₁ : Path x₀ x₁}

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Function.Injective (Homotopy p₀ p₁) (I × I -> X) (⇑)
  proof: DFunLike.coe_injective

@[simp]

中文:
定理 coeFn_injective
  结论: @Function.Injective (Homotopy p₀ p₁) (I × I -> X) (⇑)
  证明: DFunLike.coe_injective

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I -> X) (⇑) :=
  DFunLike.coe_injective

@[simp]
/--
theorem `source` / 定理 `source`

English:
theorem source
  given: (F : Homotopy p₀ p₁) (t : I)
  statement: F (t, 0) = x₀
  proof: calc F (t, 0) = p₀ 0 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inl rfl)
  _ = x₀ := p₀.source

@[simp]

中文:
定理 source
  条件: (F : Homotopy p₀ p₁) (t : I)
  结论: F (t, 0) = x₀
  证明: calc F (t, 0) = p₀ 0 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inl rfl)
  _ = x₀ := p₀.source

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.eq_fst, HomotopyRel, eq_fst, source
-/
theorem source (F : Homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ :=
  calc F (t, 0) = p₀ 0 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inl rfl)
  _ = x₀ := p₀.source

@[simp]
/--
theorem `target` / 定理 `target`

English:
theorem target
  given: (F : Homotopy p₀ p₁) (t : I)
  statement: F (t, 1) = x₁
  proof: calc F (t, 1) = p₀ 1 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inr rfl)
  _ = x₁ := p₀.target

中文:
定理 target
  条件: (F : Homotopy p₀ p₁) (t : I)
  结论: F (t, 1) = x₁
  证明: calc F (t, 1) = p₀ 1 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inr rfl)
  _ = x₁ := p₀.target

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.eq_fst, HomotopyRel, eq_fst, target
-/
theorem target (F : Homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ :=
  calc F (t, 1) = p₀ 1 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inr rfl)
  _ = x₁ := p₀.target

/-- Evaluating a path homotopy at an intermediate point, giving us a `Path`.
-/
@[simps]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (F : Homotopy p₀ p₁) (t : I)
  body: F.toHomotopy.curry t
  source' := by simp
  target' := by simp

@[simp]

中文:
定义 eval
  签名: (F : Homotopy p₀ p₁) (t : I)
  定义体: F.toHomotopy.curry t
  source' := by simp
  target' := by simp

@[simp]

Depends on / 依赖: F.toHomotopy.curry, toHomotopy
-/
def eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where
  toFun := F.toHomotopy.curry t
  source' := by simp
  target' := by simp

@[simp]
/--
theorem `eval_zero` / 定理 `eval_zero`

English:
theorem eval_zero
  given: (F : Homotopy p₀ p₁)
  statement: F.eval 0 = p₀
  proof: by
  ext t
  simp

@[simp]

中文:
定理 eval_zero
  条件: (F : Homotopy p₀ p₁)
  结论: F.eval 0 = p₀
  证明: by
  ext t
  simp

@[simp]
-/
theorem eval_zero (F : Homotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp

@[simp]
/--
theorem `eval_one` / 定理 `eval_one`

English:
theorem eval_one
  given: (F : Homotopy p₀ p₁)
  statement: F.eval 1 = p₁
  proof: by
  ext t
  simp

中文:
定理 eval_one
  条件: (F : Homotopy p₀ p₁)
  结论: F.eval 1 = p₁
  证明: by
  ext t
  simp
-/
theorem eval_one (F : Homotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp

end

section

variable {p₀ p₁ p₂ : Path x₀ x₁}

/-- Given a path `p`, we can define a `Homotopy p p` by `F (t, x) = p x`.
-/
@[simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (p : Path x₀ x₁)
  body: ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}

中文:
定义 refl
  签名: (p : Path x₀ x₁)
  定义体: ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.refl, HomotopyRel, p.toContinuousMap, toContinuousMap
-/
def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}

/-- Given a `Homotopy p₀ p₁`, we can define a `Homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps!]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (F : Homotopy p₀ p₁)
  body: ContinuousMap.HomotopyRel.symm F

@[simp]

中文:
定义 symm
  签名: (F : Homotopy p₀ p₁)
  定义体: ContinuousMap.HomotopyRel.symm F

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.symm, HomotopyRel
-/
def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (F : Homotopy p₀ p₁)
  statement: F.symm.symm = F
  proof: ContinuousMap.HomotopyRel.symm_symm F

中文:
定理 symm_symm
  条件: (F : Homotopy p₀ p₁)
  结论: F.symm.symm = F
  证明: ContinuousMap.HomotopyRel.symm_symm F

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.symm_symm, HomotopyRel, symm_symm
-/
theorem symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = F :=
  ContinuousMap.HomotopyRel.symm_symm F

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ -> Homotopy p₁ p₀)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ -> Homotopy p₁ p₀)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ -> Homotopy p₁ p₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂)
  body: ContinuousMap.HomotopyRel.trans F G

中文:
定义 trans
  签名: (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂)
  定义体: ContinuousMap.HomotopyRel.trans F G

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.trans, HomotopyRel
-/
def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I)
  proof: ContinuousMap.HomotopyRel.trans_apply _ _ _

中文:
定理 trans_apply
  条件: (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I)
  证明: ContinuousMap.HomotopyRel.trans_apply _ _ _

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.trans_apply, HomotopyRel, trans_apply
-/
theorem trans_apply (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I) :
    (F.trans G) x =
      if h : (x.1 : Real) <= 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂)
  proof: ContinuousMap.HomotopyRel.symm_trans _ _

中文:
定理 symm_trans
  条件: (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂)
  证明: ContinuousMap.HomotopyRel.symm_trans _ _

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.symm_trans, HomotopyRel, symm_trans
-/
theorem symm_trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ContinuousMap.HomotopyRel.symm_trans _ _

/-- Casting a `Homotopy p₀ p₁` to a `Homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`. -/
@[simps!]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁)
  body: ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

中文:
定义 cast
  签名: {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁)
  定义体: ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.cast, HomotopyRel, congr_arg
-/
def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

/-- If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`. -/
@[simp]
/--
Definition of `pathCast` / `pathCast` 的定义

English:
definition pathCast
  signature: {x x' y y' : X} {p q : Path x y} (F : p.Homotopy q) (hx : x' = x) (hy : y' = y)
  body: F

中文:
定义 pathCast
  签名: {x x' y y' : X} {p q : Path x y} (F : p.Homotopy q) (hx : x' = x) (hy : y' = y)
  定义体: F
-/
def pathCast {x x' y y' : X} {p q : Path x y} (F : p.Homotopy q) (hx : x' = x) (hy : y' = y) :
    (p.cast hx hy).Homotopy (q.cast hx hy) :=
  F

end

section

variable {p₀ q₀ : Path x₀ x₁} {p₁ q₁ : Path x₁ x₂}

/--
Definition of `hcomp` / `hcomp` 的定义

English:
definition hcomp
  signature: (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁)
  body: if (x.2 : Real) <= 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by fun_prop)).continuousOn
    (G.toHomotopy.continuous.comp (by 

中文:
定义 hcomp
  签名: (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁)
  定义体: if (x.2 : Real) <= 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by fun_prop)).continuousOn
    (G.toHomotopy.continuous.comp (by 

Depends on / 依赖: F.eval, F.toHomotopy.continuous.comp, G.eval, G.toHomotopy.continuous.comp, Path.trans, Set.mem_single, continuous, continuousOn, continuous_const, continuous_if_le, continuous_induced_dom, continuous_induced_dom.comp, continuous_snd, continuous_toFun, extend, fun_prop, map_one_left, map_zero_left, mem_single, toHomotopy
-/
def hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (q₀.trans q₁) where
  toFun x :=
    if (x.2 : Real) <= 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by fun_prop)).continuousOn
    (G.toHomotopy.continuous.comp (by fun_prop)).continuousOn fun x hx => by norm_num [hx]
  map_zero_left x := by simp [Path.trans]
  map_one_left x := by simp [Path.trans]
  prop' x t ht := by
    rcases ht with ht | ht
    · norm_num [ht]
    · rw [Set.mem_singleton_iff] at ht
      norm_num [ht]

/--
theorem `hcomp_apply` / 定理 `hcomp_apply`

English:
theorem hcomp_apply
  given: (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I)
  proof: show ite _ _ _ = _ by split_ifs <;> exact Path.extend_apply _ _

中文:
定理 hcomp_apply
  条件: (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I)
  证明: show ite _ _ _ = _ by split_ifs <;> exact Path.extend_apply _ _

Depends on / 依赖: Path.extend_apply, extend_apply, split_ifs
-/
theorem hcomp_apply (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : Real) <= 1 / 2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1
          ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_apply _ _

/--
theorem `hcomp_half` / 定理 `hcomp_half`

English:
theorem hcomp_half
  given: (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I)
  proof: show ite _ _ _ = _ by norm_num

中文:
定理 hcomp_half
  条件: (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I)
  证明: show ite _ _ _ = _ by norm_num
-/
theorem hcomp_half (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1 / 2, by norm_num, by norm_num⟩) = x₁ :=
  show ite _ _ _ = _ by norm_num

end

/--
Definition of `reparam` / `reparam` 的定义

English:
definition reparam
  signature: (p : Path x₀ x₁) (f : I -> I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
  body: p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : Real) • (x.2 : Real) + (x.1 : Real) • (f x.2 : Real) in I from
      convex_Icc _ _ x.2.2 (f x.2).2 (by unit_interval) (by unit_interval) (by simp)⟩
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
  prop' t x hx := by
    rcases hx wit

中文:
定义 reparam
  签名: (p : Path x₀ x₁) (f : I -> I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
  定义体: p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : Real) • (x.2 : Real) + (x.1 : Real) • (f x.2 : Real) in I from
      convex_Icc _ _ x.2.2 (f x.2).2 (by unit_interval) (by unit_interval) (by simp)⟩
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
  prop' t x hx := by
    rcases hx wit
-/
def reparam (p : Path x₀ x₁) (f : I -> I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Homotopy p (p.reparam f hf hf₀ hf₁) where
  toFun x := p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : Real) • (x.2 : Real) + (x.1 : Real) • (f x.2 : Real) in I from
      convex_Icc _ _ x.2.2 (f x.2).2 (by unit_interval) (by unit_interval) (by simp)⟩
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp [hf₀]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp [hf₁]
  continuous_toFun := by fun_prop

/-- Suppose `F : Homotopy p q`. Then we have a `Homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
/--
Definition of `symm₂` / `symm₂` 的定义

English:
definition symm₂
  signature: {p q : Path x₀ x₁} (F : p.Homotopy q)
  body: F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp

中文:
定义 symm₂
  签名: {p q : Path x₀ x₁} (F : p.Homotopy q)
  定义体: F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
-/
def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun x := F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp

/--
Given `F : Homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.map f.continuous` to
`q.map f.continuous`.
-/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y))
  body: f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    rcases hx with hx | hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]

中文:
定义 map
  签名: {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y))
  定义体: f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    rcases hx with hx | hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]
-/
def map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) :
    Homotopy (p.map f.continuous) (q.map f.continuous) where
  toFun := f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    rcases hx with hx | hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]

end Homotopy

/--
Definition of `Homotopic` / `Homotopic` 的定义

English:
definition Homotopic
  signature: (p₀ p₁ : Path x₀ x₁)
  body: Nonempty (p₀.Homotopy p₁)

中文:
定义 Homotopic
  签名: (p₀ p₁ : Path x₀ x₁)
  定义体: Nonempty (p₀.Homotopy p₁)

Depends on / 依赖: Homotopy, Nonempty
-/
def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)

namespace Homotopic

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (p : Path x₀ x₁)
  statement: p.Homotopic p
  proof: ⟨Homotopy.refl p⟩

@[symm]

中文:
定理 refl
  条件: (p : Path x₀ x₁)
  结论: p.Homotopic p
  证明: ⟨Homotopy.refl p⟩

@[symm]

Depends on / 依赖: Homotopy, Homotopy.refl
-/
theorem refl (p : Path x₀ x₁) : p.Homotopic p :=
  ⟨Homotopy.refl p⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: ⦃p₀ p₁
  statement: Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀
  proof: h.map Homotopy.symm

中文:
定理 symm
  条件: ⦃p₀ p₁
  结论: Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀
  证明: h.map Homotopy.symm

Depends on / 依赖: Homotopy, Homotopy.symm, h.map
-/
theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀ :=
  h.map Homotopy.symm

/--
theorem `symm₂` / 定理 `symm₂`

English:
theorem symm₂
  given: {p q : Path x₀ x₁} (h : p.Homotopic q)
  statement: p.symm.Homotopic q.symm
  proof: h.map Homotopy.symm₂

@[trans]

中文:
定理 symm₂
  条件: {p q : Path x₀ x₁} (h : p.Homotopic q)
  结论: p.symm.Homotopic q.symm
  证明: h.map Homotopy.symm₂

@[trans]

Depends on / 依赖: Homotopy, Homotopy.symm, h.map
-/
theorem symm₂ {p q : Path x₀ x₁} (h : p.Homotopic q) : p.symm.Homotopic q.symm :=
  h.map Homotopy.symm₂

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: ⦃p₀ p₁ p₂
  statement: Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
  proof: h₀.map2 Homotopy.trans h₁

中文:
定理 trans
  条件: ⦃p₀ p₁ p₂
  结论: Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
  证明: h₀.map2 Homotopy.trans h₁

Depends on / 依赖: Homotopy, Homotopy.trans
-/
theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
    p₀.Homotopic p₂ :=
  h₀.map2 Homotopy.trans h₁

/--
theorem `equivalence` / 定理 `equivalence`

English:
theorem equivalence
  statement: Equivalence (@Homotopic X _ x₀ x₁)
  proof: ⟨refl, (symm ·), (trans · ·)⟩

中文:
定理 equivalence
  结论: Equivalence (@Homotopic X _ x₀ x₁)
  证明: ⟨refl, (symm ·), (trans · ·)⟩
-/
theorem equivalence : Equivalence (@Homotopic X _ x₀ x₁) :=
  ⟨refl, (symm ·), (trans · ·)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEquiv (Path x₀ x₁) Homotopic
  body: refl
  symm := symm
  trans := trans

nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f

中文:
实例 :
  签名: IsEquiv (Path x₀ x₁) Homotopic
  定义体: refl
  symm := symm
  trans := trans

nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f
-/
instance : IsEquiv (Path x₀ x₁) Homotopic where
  refl := refl
  symm := symm
  trans := trans

nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f

/--
theorem `hcomp` / 定理 `hcomp`

English:
theorem hcomp
  statement: {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁)
  proof: hp.map2 Homotopy.hcomp hq

中文:
定理 hcomp
  结论: {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁)
  证明: hp.map2 Homotopy.hcomp hq

Depends on / 依赖: Homotopy, Homotopy.hcomp, hp.map2
-/
theorem hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁)
    (hq : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans q₁) :=
  hp.map2 Homotopy.hcomp hq

/--
theorem `pathCast` / 定理 `pathCast`

English:
theorem pathCast
  given: {p q : Path x₀ x₁} (hpq : p.Homotopic q) (hsource : x₂ = x₀) (htarget : x₃ = x₁)
  proof: hpq

中文:
定理 pathCast
  条件: {p q : Path x₀ x₁} (hpq : p.Homotopic q) (hsource : x₂ = x₀) (htarget : x₃ = x₁)
  证明: hpq
-/
theorem pathCast {p q : Path x₀ x₁} (hpq : p.Homotopic q) (hsource : x₂ = x₀) (htarget : x₃ = x₁) :
    (p.cast hsource htarget).Homotopic (q.cast hsource htarget) :=
  hpq

/--
The setoid on `Path`s defined by the equivalence relation `Path.Homotopic`. That is, two paths are
equivalent if there is a `Homotopy` between them.
-/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: (x₀ x₁ : X)
  body: ⟨Homotopic, equivalence⟩

中文:
定义 setoid
  签名: (x₀ x₁ : X)
  定义体: ⟨Homotopic, equivalence⟩
-/
protected def setoid (x₀ x₁ : X) : Setoid (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩

/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  signature: (x₀ x₁ : X)
  body: Quotient (Homotopic.setoid x₀ x₁)

中文:
定义 Quotient
  签名: (x₀ x₁ : X)
  定义体: Quotient (Homotopic.setoid x₀ x₁)
-/
protected def Quotient (x₀ x₁ : X) :=
  Quotient (Homotopic.setoid x₀ x₁)

attribute [local instance] Homotopic.setoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Homotopic.Quotient () ())
  body: ⟨Quotient.mk' Path.refl ()⟩

中文:
实例 :
  签名: Inhabited (Homotopic.Quotient () ())
  定义体: ⟨Quotient.mk' Path.refl ()⟩

Depends on / 依赖: Path.refl, Quotient, Quotient.mk
-/
instance : Inhabited (Homotopic.Quotient () ()) :=
⟨Quotient.mk' Path.refl ()⟩

namespace Quotient

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (p : Path x₀ x₁)
  body: Quotient.mk' p

中文:
定义 mk
  签名: (p : Path x₀ x₁)
  定义体: Quotient.mk' p

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk (p : Path x₀ x₁) : Path.Homotopic.Quotient x₀ x₁ :=
  Quotient.mk' p

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (@mk X _ x₀ x₁)
  proof: Quotient.mk'_surjective

中文:
定理 mk_surjective
  结论: Function.Surjective (@mk X _ x₀ x₁)
  证明: Quotient.mk'_surjective

Depends on / 依赖: Quotient, Quotient.mk, _surjective
-/
theorem mk_surjective : Function.Surjective (@mk X _ x₀ x₁) :=
  Quotient.mk'_surjective

/--
theorem `mk'_eq_mk` / 定理 `mk'_eq_mk`

English:
theorem mk'_eq_mk
  given: (p : Path x₀ x₁)
  statement: Quotient.mk' p = mk p
  proof: rfl

中文:
定理 mk'_eq_mk
  条件: (p : Path x₀ x₁)
  结论: Quotient.mk' p = mk p
  证明: rfl
-/
@[simp] theorem mk'_eq_mk (p : Path x₀ x₁) : Quotient.mk' p = mk p := rfl
/--
theorem `mk''_eq_mk` / 定理 `mk''_eq_mk`

English:
theorem mk''_eq_mk
  given: (p : Path x₀ x₁)
  statement: Quotient.mk'' p = mk p
  proof: rfl

中文:
定理 mk''_eq_mk
  条件: (p : Path x₀ x₁)
  结论: Quotient.mk'' p = mk p
  证明: rfl
-/
@[simp] theorem mk''_eq_mk (p : Path x₀ x₁) : Quotient.mk'' p = mk p := rfl

/--
theorem `exact` / 定理 `exact`

English:
theorem exact
  given: {p q : Path x₀ x₁} (h : Quotient.mk p = Quotient.mk q)
  proof: by
  exact _root_.Quotient.exact h

中文:
定理 exact
  条件: {p q : Path x₀ x₁} (h : Quotient.mk p = Quotient.mk q)
  证明: by
  exact _root_.Quotient.exact h

Depends on / 依赖: Quotient, _root_, _root_.Quotient.exact
-/
theorem exact {p q : Path x₀ x₁} (h : Quotient.mk p = Quotient.mk q) :
    Homotopic p q := by
  exact _root_.Quotient.exact h

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {p q : Path x₀ x₁}
  statement: mk p = mk q ↔ Homotopic p q
  proof: _root_.Quotient.eq

中文:
定理 eq
  条件: {p q : Path x₀ x₁}
  结论: mk p = mk q ↔ Homotopic p q
  证明: _root_.Quotient.eq

Depends on / 依赖: Quotient, _root_, _root_.Quotient.eq
-/
theorem eq {p q : Path x₀ x₁} : mk p = mk q ↔ Homotopic p q :=
  _root_.Quotient.eq

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`.
-/
@[induction_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {x y : X} {motive : Homotopic.Quotient x y -> Prop}
  proof: Quot.ind

中文:
定理 ind
  条件: {x y : X} {motive : Homotopic.Quotient x y -> 命题}
  证明: Quot.ind
-/
protected theorem ind {x y : X} {motive : Homotopic.Quotient x y -> Prop} :
    (mk : (a : Path x y) -> motive (Quotient.mk a)) -> (q : Homotopic.Quotient x y) -> motive q :=
  Quot.ind

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`. This is the two-variable version of `ind`.
-/
@[elab_as_elim]
/--
theorem `ind₂` / 定理 `ind₂`

English:
theorem ind₂
  statement: {Y : Type*} [TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}
  proof: by
  induction q₀ using Quot.ind with | mk a =>
  induction q₁ using Quot.ind with | mk b =>
  exact mk a b

中文:
定理 ind₂
  结论: {Y : 类型} [TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}
  证明: by
  induction q₀ using Quot.ind with | mk a =>
  induction q₁ using Quot.ind with | mk b =>
  exact mk a b
-/
protected theorem ind₂ {Y : Type*} [TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}
    {motive : Homotopic.Quotient x₀ y₀ -> Path.Homotopic.Quotient x₁ y₁ -> Prop}
    (mk : (a : Path x₀ y₀) -> (b : Path x₁ y₁) -> motive (Quotient.mk a) (Quotient.mk b))
    (q₀ : Homotopic.Quotient x₀ y₀) (q₁ : Path.Homotopic.Quotient x₁ y₁) : motive q₀ q₁ := by
  induction q₀ using Quot.ind with | mk a =>
  induction q₁ using Quot.ind with | mk b =>
  exact mk a b

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (x : X)
  body: mk (Path.refl x)

@[simp, grind =]

中文:
定义 refl
  签名: (x : X)
  定义体: mk (Path.refl x)

@[simp, grind =]

Depends on / 依赖: Path.refl
-/
def refl (x : X) : Path.Homotopic.Quotient x x :=
  mk (Path.refl x)

@[simp, grind =]
/--
theorem `mk_refl` / 定理 `mk_refl`

English:
theorem mk_refl
  given: (x : X)
  statement: mk (Path.refl x) = refl x
  proof: rfl

中文:
定理 mk_refl
  条件: (x : X)
  结论: mk (Path.refl x) = refl x
  证明: rfl
-/
theorem mk_refl (x : X) : mk (Path.refl x) = refl x :=
  rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (P : Path.Homotopic.Quotient x₀ x₁)
  body: _root_.Quotient.map Path.symm (fun _ _ h => Homotopic.symm₂ h) P

@[simp, grind =]

中文:
定义 symm
  签名: (P : Path.Homotopic.Quotient x₀ x₁)
  定义体: _root_.Quotient.map Path.symm (fun _ _ h => Homotopic.symm₂ h) P

@[simp, grind =]

Depends on / 依赖: Homotopic, Homotopic.symm, Path.symm, Quotient, _root_, _root_.Quotient.map
-/
def symm (P : Path.Homotopic.Quotient x₀ x₁) : Path.Homotopic.Quotient x₁ x₀ :=
  _root_.Quotient.map Path.symm (fun _ _ h => Homotopic.symm₂ h) P

@[simp, grind =]
/--
theorem `mk_symm` / 定理 `mk_symm`

English:
theorem mk_symm
  given: (P : Path x₀ x₁)
  statement: mk P.symm = symm (mk P)
  proof: rfl

中文:
定理 mk_symm
  条件: (P : Path x₀ x₁)
  结论: mk P.symm = symm (mk P)
  证明: rfl
-/
theorem mk_symm (P : Path x₀ x₁) : mk P.symm = symm (mk P) :=
  rfl

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
  body: _root_.Quotient.map (fun p => p.cast hx hy) (fun _ _ h => h) γ

@[simp, grind =]

中文:
定义 cast
  签名: {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
  定义体: _root_.Quotient.map (fun p => p.cast hx hy) (fun _ _ h => h) γ

@[simp, grind =]

Depends on / 依赖: Quotient, _root_, _root_.Quotient.map, p.cast
-/
def cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y) :
    Homotopic.Quotient x' y' :=
  _root_.Quotient.map (fun p => p.cast hx hy) (fun _ _ h => h) γ

@[simp, grind =]
/--
theorem `mk_cast` / 定理 `mk_cast`

English:
theorem mk_cast
  given: {x y : X} (P : Path x y) {x' y'} (hx : x' = x) (hy : y' = y)
  proof: rfl

@[simp, grind =]

中文:
定理 mk_cast
  条件: {x y : X} (P : Path x y) {x' y'} (hx : x' = x) (hy : y' = y)
  证明: rfl

@[simp, grind =]
-/
theorem mk_cast {x y : X} (P : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) :
    mk (P.cast hx hy) = (mk P).cast hx hy :=
  rfl

@[simp, grind =]
/--
theorem `cast_rfl_rfl` / 定理 `cast_rfl_rfl`

English:
theorem cast_rfl_rfl
  given: {x y : X} (γ : Homotopic.Quotient x y)
  statement: γ.cast rfl rfl = γ
  proof: by
  induction γ using Quotient.ind with | mk γ =>
  rfl

@[simp, grind =]

中文:
定理 cast_rfl_rfl
  条件: {x y : X} (γ : Homotopic.Quotient x y)
  结论: γ.cast rfl rfl = γ
  证明: by
  induction γ using Quotient.ind with | mk γ =>
  rfl

@[simp, grind =]

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem cast_rfl_rfl {x y : X} (γ : Homotopic.Quotient x y) : γ.cast rfl rfl = γ := by
  induction γ using Quotient.ind with | mk γ =>
  rfl

@[simp, grind =]
/--
theorem `cast_cast` / 定理 `cast_cast`

English:
theorem cast_cast
  statement: {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
  proof: by
  induction γ using Quotient.ind with | mk γ =>
  rfl

中文:
定理 cast_cast
  结论: {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
  证明: by
  induction γ using Quotient.ind with | mk γ =>
  rfl

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem cast_cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
    {x'' y''} (hx' : x'' = x') (hy' : y'' = y') :
    (γ.cast hx hy).cast hx' hy' = γ.cast (hx'.trans hx) (hy'.trans hy) := by
  induction γ using Quotient.ind with | mk γ =>
  rfl

/--
theorem `cast_heq` / 定理 `cast_heq`

English:
theorem cast_heq
  given: {x y x' y' : X} (hx : x' = x) (hy : y' = y) {γ : Homotopic.Quotient x y}
  proof: by
  cases hx; cases hy; exact heq_of_eq γ.cast_rfl_rfl

中文:
定理 cast_heq
  条件: {x y x' y' : X} (hx : x' = x) (hy : y' = y) {γ : Homotopic.Quotient x y}
  证明: by
  cases hx; cases hy; exact heq_of_eq γ.cast_rfl_rfl

Depends on / 依赖: cast_rfl_rfl, heq_of_eq
-/
theorem cast_heq {x y x' y' : X} (hx : x' = x) (hy : y' = y) {γ : Homotopic.Quotient x y} :
    γ.cast hx hy ≍ γ := by
  cases hx; cases hy; exact heq_of_eq γ.cast_rfl_rfl

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂)
  body: Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁

@[simp, grind =]

中文:
定义 trans
  签名: (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂)
  定义体: Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁

@[simp, grind =]

Depends on / 依赖: Path.trans, Quotient, Quotient.map
-/
def trans (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
    Path.Homotopic.Quotient x₀ x₂ :=
  Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁

@[simp, grind =]
/--
theorem `mk_trans` / 定理 `mk_trans`

English:
theorem mk_trans
  given: (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂)
  proof: rfl

中文:
定理 mk_trans
  条件: (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂)
  证明: rfl
-/
theorem mk_trans (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂) :
    mk (P₀.trans P₁) = Quotient.trans (mk P₀) (mk P₁) :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y))
  body: _root_.Quotient.map
    (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀

中文:
定义 map
  签名: (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y))
  定义体: _root_.Quotient.map
    (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀

Depends on / 依赖: Homotopic, Path.Homotopic.map, Quotient, _root_, _root_.Quotient.map, continuous, f.continuous, q.map
-/
def map (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁) :=
  _root_.Quotient.map
    (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀

/--
theorem `mk_map` / 定理 `mk_map`

English:
theorem mk_map
  given: (P₀ : Path x₀ x₁) (f : C(X, Y))
  statement: mk (P₀.map f.continuous) = map (mk P₀) f
  proof: rfl

中文:
定理 mk_map
  条件: (P₀ : Path x₀ x₁) (f : C(X, Y))
  结论: mk (P₀.map f.continuous) = map (mk P₀) f
  证明: rfl
-/
theorem mk_map (P₀ : Path x₀ x₁) (f : C(X, Y)) : mk (P₀.map f.continuous) = map (mk P₀) f :=
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: {Z} [TopologicalSpace Z] {p : Path.Homotopic.Quotient x₀ x₁}
  proof: by
  rcases p; rfl

中文:
定理 map_comp
  结论: {Z} [TopologicalSpace Z] {p : Path.Homotopic.Quotient x₀ x₁}
  证明: by
  rcases p; rfl
-/
theorem map_comp {Z} [TopologicalSpace Z] {p : Path.Homotopic.Quotient x₀ x₁}
    {f : C(X, Y)} {g : C(Y, Z)} : p.map (g.comp f) = (p.map f).map g := by
  rcases p; rfl

/--
theorem `map_cast` / 定理 `map_cast`

English:
theorem map_cast
  statement: {x y : X} (p : Homotopic.Quotient x y) {x' y'} {hx : x' = x} {hy : y' = y}
  proof: by
  rcases p; rfl

中文:
定理 map_cast
  结论: {x y : X} (p : Homotopic.Quotient x y) {x' y'} {hx : x' = x} {hy : y' = y}
  证明: by
  rcases p; rfl
-/
theorem map_cast {x y : X} (p : Homotopic.Quotient x y) {x' y'} {hx : x' = x} {hy : y' = y}
    {f : C(X, Y)} : (p.cast hx hy).map f = (p.map f).cast congr(f $hx) congr(f $hy) := by
  rcases p; rfl

end Quotient

set_option backward.isDefEq.respectTransparency false in
-- Porting note: we didn't previously need the `α := ...` and `β := ...` hints.
/--
theorem `hpath_hext` / 定理 `hpath_hext`

English:
theorem hpath_hext
  given: {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : forall t, p₁ t = p₂ t)
  proof: by
  obtain rfl : x₀ = x₂ := by convert! hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert! hp 1 <;> simp
  rw [heq_iff_eq]; congr; ext t; exact hp t

中文:
定理 hpath_hext
  条件: {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : 对任意 t, p₁ t = p₂ t)
  证明: by
  obtain rfl : x₀ = x₂ := by convert! hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert! hp 1 <;> simp
  rw [heq_iff_eq]; congr; ext t; exact hp t

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient, Quotient, convert, heq_iff_eq
-/
theorem hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : forall t, p₁ t = p₂ t) :
    HEq (α := Path.Homotopic.Quotient _ _) ⟦p₁⟧ (β := Path.Homotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert! hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert! hp 1 <;> simp
  rw [heq_iff_eq]; congr; ext t; exact hp t

end Homotopic

/-- A path `Path x₀ x₁` generates a homotopy between constant functions `fun _ ↦ x₀` and
`fun _ ↦ x₁`. -/
@[simps!]
/--
Definition of `toHomotopyConst` / `toHomotopyConst` 的定义

English:
definition toHomotopyConst
  signature: (p : Path x₀ x₁)
  body: p.toContinuousMap.comp ContinuousMap.fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

中文:
定义 toHomotopyConst
  签名: (p : Path x₀ x₁)
  定义体: p.toContinuousMap.comp ContinuousMap.fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

Depends on / 依赖: ContinuousMap, ContinuousMap.fst, p.toContinuousMap.comp, toContinuousMap
-/
def toHomotopyConst (p : Path x₀ x₁) :
    (ContinuousMap.const Y x₀).Homotopy (ContinuousMap.const Y x₁) where
  toContinuousMap := p.toContinuousMap.comp ContinuousMap.fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

end Path

/-- Two constant continuous maps with nonempty domain are homotopic if and only if their values are
joined by a path in the codomain. -/
@[simp]
/--
theorem `ContinuousMap.homotopic_const_iff` / 定理 `ContinuousMap.homotopic_const_iff`

English:
theorem ContinuousMap.homotopic_const_iff
  given: [Nonempty Y]
  proof: by
  inhabit Y
  refine ⟨fun ⟨H⟩ => ⟨⟨(H.toContinuousMap.comp .prodSwap).curry default, ?_, ?_⟩⟩,
    fun ⟨p⟩ => ⟨p.toHomotopyConst⟩⟩ <;> simp

中文:
定理 ContinuousMap.homotopic_const_iff
  条件: [Nonempty Y]
  证明: by
  inhabit Y
  refine ⟨fun ⟨H⟩ => ⟨⟨(H.toContinuousMap.comp .prodSwap).curry default, ?_, ?_⟩⟩,
    fun ⟨p⟩ => ⟨p.toHomotopyConst⟩⟩ <;> simp

Depends on / 依赖: H.toContinuousMap.comp, inhabit, p.toHomotopyConst, prodSwap, toContinuousMap, toHomotopyConst
-/
theorem ContinuousMap.homotopic_const_iff [Nonempty Y] :
    (ContinuousMap.const Y x₀).Homotopic (ContinuousMap.const Y x₁) ↔ Joined x₀ x₁ := by
  inhabit Y
  refine ⟨fun ⟨H⟩ => ⟨⟨(H.toContinuousMap.comp .prodSwap).curry default, ?_, ?_⟩⟩,
    fun ⟨p⟩ => ⟨p.toHomotopyConst⟩⟩ <;> simp

namespace ContinuousMap.Homotopy

/-- Given a homotopy `H : f ∼ g`, get the path traced by the point `x` as it moves from
`f x` to `g x`.
-/
@[simps]
/--
Definition of `evalAt` / `evalAt` 的定义

English:
definition evalAt
  signature: {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X)
  body: H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x

@[simp]

中文:
定义 evalAt
  签名: {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X)
  定义体: H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x

@[simp]
-/
def evalAt {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) : Path (f x) (g x) where
  toFun t := H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x

@[simp]
/--
theorem `pathExtend_evalAt` / 定理 `pathExtend_evalAt`

English:
theorem pathExtend_evalAt
  given: {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
  proof: rfl

中文:
定理 pathExtend_evalAt
  条件: {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
  证明: rfl
-/
theorem pathExtend_evalAt {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    (H.evalAt x).extend = (fun t => H.extend t x) := rfl

end ContinuousMap.Homotopy
