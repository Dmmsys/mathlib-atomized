/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
module

public import Batteries.Data.Fin.Fold
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Subpaths and concatenation of paths

This file defines `Path.subpath` as a restriction of a path to a subinterval, reparameterized to
have domain `[0, 1]` and possibly with a reverse of direction. It then defines `Path.concat` as
a way to concatenate finite sequences of paths with compatible endpoints.

The main result `Path.Homotopy.concatSubpath` shows that subpaths concatenate nicely.
In particular: following the subpaths of `γ` from `t i` to `t (i + 1)` for `0 ≤ i < n` is
homotopic to the subpath of `γ` from `t 0` to `t n`.

## TODO

Prove that `Path.truncateOfLE` and `Path.subpath` are reparameterizations of each other.
(`Path.subpath` is still a useful definition because it works without assuming an order on `t₀` and
`t₁`, and is convenient for concrete manipulations.)
-/

@[expose] public noncomputable section

open Fin Function Set unitInterval

variable {X : Type*} [TopologicalSpace X] {a b : X}

namespace Path

/-!
## Subpaths
-/

@[deprecated (since := "2026-03-20")]
alias subpathAux := Icc.convexComb

@[deprecated (since := "2026-03-20")]
alias subpathAux_zero := Icc.convexComb_zero

@[deprecated (since := "2026-03-20")]
alias subpathAux_one := Icc.convexComb_one

@[deprecated (since := "2026-03-20")]
alias subpathAux_continuous := Icc.continuous_convexComb_prod

/--
Definition of `subpath` / `subpath` 的定义

English:
definition subpath
  signature: (γ : Path a b) (t₀ t₁ : I)
  body: γ ∘ Icc.convexComb t₀ t₁
  source' := by simp
  target' := by simp

中文:
定义 subpath
  签名: (γ : 道路 a b) (t₀ t₁ : I)
  定义体: γ ∘ Icc.convexComb t₀ t₁
  source' := by simp
  target' := by simp

Depends on / 依赖: Icc.convexComb, convexComb
-/
def subpath (γ : Path a b) (t₀ t₁ : I) : Path (γ t₀) (γ t₁) where
  toFun := γ ∘ Icc.convexComb t₀ t₁
  source' := by simp
  target' := by simp

/-- Reversing `γ.subpath t₀ t₁` results in `γ.subpath t₁ t₀`. -/
@[simp]
/--
theorem `symm_subpath` / 定理 `symm_subpath`

English:
theorem symm_subpath
  given: (γ : Path a b) (t₀ t₁ : I)
  statement: symm (γ.subpath t₀ t₁) = γ.subpath t₁ t₀
  proof: by
  ext s
  simp [subpath]

中文:
定理 symm_subpath
  条件: (γ : 道路 a b) (t₀ t₁ : I)
  结论: symm (γ.subpath t₀ t₁) = γ.subpath t₁ t₀
  证明: by
  ext s
  simp [subpath]

Depends on / 依赖: subpath
-/
theorem symm_subpath (γ : Path a b) (t₀ t₁ : I) : symm (γ.subpath t₀ t₁) = γ.subpath t₁ t₀ := by
  ext s
  simp [subpath]

/--
lemma `range_subpathAux` / 引理 `range_subpathAux`

English:
lemma range_subpathAux
  given: (t₀ t₁ : I)
  statement: range (Icc.convexComb t₀ t₁) = uIcc t₀ t₁
  proof: by
  rw [range_eq_iff]
  constructor
  · intro s
    exact convex_uIcc (t₀ : Real) t₁ left_mem_uIcc right_mem_uIcc
      (one_minus_nonneg s) (nonneg s) (sub_add_cancel _ _)
  · intro t (ht : (t : Real) in uIcc (t₀ : Real) (t₁ : Real))
    rw [← segment_eq_uIcc]; rw [segment_eq_image] at ht
    obta

中文:
引理 range_subpathAux
  条件: (t₀ t₁ : I)
  结论: range (闭区间.convexComb t₀ t₁) = uIcc t₀ t₁
  证明: by
  rw [range_eq_iff]
  constructor
  · intro s
    exact convex_uIcc (t₀ : Real) t₁ left_mem_uIcc right_mem_uIcc
      (one_minus_nonneg s) (nonneg s) (sub_add_cancel _ _)
  · intro t (ht : (t : Real) in uIcc (t₀ : Real) (t₁ : Real))
    rw [← segment_eq_uIcc]; rw [segment_eq_image] at ht
    obta

Depends on / 依赖: convex_uIcc, left_mem_uIcc, nonneg, one_minus_nonneg, range_eq_iff, right_mem_uIcc, segment_eq_image, segment_eq_uIcc, sub_add_cancel
-/
lemma range_subpathAux (t₀ t₁ : I) : range (Icc.convexComb t₀ t₁) = uIcc t₀ t₁ := by
  rw [range_eq_iff]
  constructor
  · intro s
    exact convex_uIcc (t₀ : Real) t₁ left_mem_uIcc right_mem_uIcc
      (one_minus_nonneg s) (nonneg s) (sub_add_cancel _ _)
  · intro t (ht : (t : Real) in uIcc (t₀ : Real) (t₁ : Real))
    rw [← segment_eq_uIcc]; rw [segment_eq_image] at ht
    obtain ⟨s, hs, hst⟩ := ht
    use ⟨s, hs⟩
    ext
    exact hst

/-- The range of a subpath is the image of the original path on the relevant interval. -/
@[simp]
/--
theorem `range_subpath` / 定理 `range_subpath`

English:
theorem range_subpath
  given: (γ : Path a b) (t₀ t₁ : I)
  proof: by
  rw [← range_subpathAux]; rw [← range_comp]; rw [subpath]; rw [coe_mk']; rw [ContinuousMap.coe_mk]

中文:
定理 range_subpath
  条件: (γ : 道路 a b) (t₀ t₁ : I)
  证明: by
  rw [← range_subpathAux]; rw [← range_comp]; rw [subpath]; rw [coe_mk']; rw [ContinuousMap.coe_mk]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, coe_mk, range_comp, range_subpathAux, subpath
-/
theorem range_subpath (γ : Path a b) (t₀ t₁ : I) :
    range (γ.subpath t₀ t₁) = γ '' (uIcc t₀ t₁) := by
  rw [← range_subpathAux]; rw [← range_comp]; rw [subpath]; rw [coe_mk']; rw [ContinuousMap.coe_mk]

/--
lemma `range_subpath_of_le` / 引理 `range_subpath_of_le`

English:
lemma range_subpath_of_le
  given: (γ : Path a b) (t₀ t₁ : I) (h : t₀ <= t₁)
  proof: by
  simp [h]

中文:
引理 range_subpath_of_le
  条件: (γ : 道路 a b) (t₀ t₁ : I) (h : t₀ <= t₁)
  证明: by
  simp [h]
-/
lemma range_subpath_of_le (γ : Path a b) (t₀ t₁ : I) (h : t₀ <= t₁) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₀ t₁) := by
  simp [h]

/--
lemma `range_subpath_of_ge` / 引理 `range_subpath_of_ge`

English:
lemma range_subpath_of_ge
  given: (γ : Path a b) (t₀ t₁ : I) (h : t₁ <= t₀)
  proof: by
  simp [h]

中文:
引理 range_subpath_of_ge
  条件: (γ : 道路 a b) (t₀ t₁ : I) (h : t₁ <= t₀)
  证明: by
  simp [h]
-/
lemma range_subpath_of_ge (γ : Path a b) (t₀ t₁ : I) (h : t₁ <= t₀) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₁ t₀) := by
  simp [h]

/-- The subpath of `γ` from `t` to `t` is just the constant path at `γ t`. -/
@[simp]
/--
theorem `subpath_self` / 定理 `subpath_self`

English:
theorem subpath_self
  given: (γ : Path a b) (t : I)
  statement: γ.subpath t t = Path.refl (γ t)
  proof: by
  ext s
  simp [subpath]

中文:
定理 subpath_self
  条件: (γ : 道路 a b) (t : I)
  结论: γ.subpath t t = 道路.refl (γ t)
  证明: by
  ext s
  simp [subpath]

Depends on / 依赖: subpath
-/
theorem subpath_self (γ : Path a b) (t : I) : γ.subpath t t = Path.refl (γ t) := by
  ext s
  simp [subpath]

/-- The subpath of `γ` from `0` to `1` is just `γ`, with a slightly different type. -/
@[simp]
/--
theorem `subpath_zero_one` / 定理 `subpath_zero_one`

English:
theorem subpath_zero_one
  given: (γ : Path a b)
  statement: γ.subpath 0 1 = γ.cast γ.source γ.target
  proof: by
  ext s
  simp [subpath]

中文:
定理 subpath_zero_one
  条件: (γ : 道路 a b)
  结论: γ.subpath 0 1 = γ.cast γ.source γ.target
  证明: by
  ext s
  simp [subpath]

Depends on / 依赖: subpath
-/
theorem subpath_zero_one (γ : Path a b) : γ.subpath 0 1 = γ.cast γ.source γ.target := by
  ext s
  simp [subpath]

/-- For a path `γ`, `γ.subpath` gives a "continuous family of paths", by which we mean
the uncurried function which maps `(t₀, t₁, s)` to `γ.subpath t₀ t₁ s` is continuous. -/
@[continuity]
/--
theorem `subpath_continuous_family` / 定理 `subpath_continuous_family`

English:
theorem subpath_continuous_family
  given: (γ : Path a b)
  proof: Continuous.comp' (map_continuous γ) Set.Icc.continuous_convexComb_prod

中文:
定理 subpath_continuous_family
  条件: (γ : 道路 a b)
  证明: Continuous.comp' (map_continuous γ) Set.Icc.continuous_convexComb_prod

Depends on / 依赖: Continuous, Continuous.comp, Set.Icc.continuous_convexComb_prod, continuous_convexComb_prod, map_continuous
-/
theorem subpath_continuous_family (γ : Path a b) :
    Continuous (fun x => γ.subpath x.1 x.2.1 x.2.2 : I × I × I -> X) :=
  Continuous.comp' (map_continuous γ) Set.Icc.continuous_convexComb_prod

namespace Homotopy

/--
Definition of `subpathTransSubpathRefl` / `subpathTransSubpathRefl` 的定义

English:
definition subpathTransSubpathRefl
  signature: (γ : Path a b) (t₀ t₁ t₂ : I)
  body: ((γ.subpath t₀ (Icc.convexComb t₁ t₂ x.1)).trans (γ.subpath _ t₂)) x.2
  continuous_toFun := by
    let γ₁ (t : I) := γ.subpath t₀ (Icc.convexComb t₁ t₂ t)
    let γ₂ (t : I) := γ.subpath (Icc.convexComb t₁ t₂ t) t₂
    refine Path.trans_continuous_family γ₁ ?_ γ₂ ?_ <;>
    refine γ.subpath_continu

中文:
定义 subpathTransSubpathRefl
  签名: (γ : 道路 a b) (t₀ t₁ t₂ : I)
  定义体: ((γ.subpath t₀ (Icc.convexComb t₁ t₂ x.1)).trans (γ.subpath _ t₂)) x.2
  continuous_toFun := by
    let γ₁ (t : I) := γ.subpath t₀ (Icc.convexComb t₁ t₂ t)
    let γ₂ (t : I) := γ.subpath (Icc.convexComb t₁ t₂ t) t₂
    refine Path.trans_continuous_family γ₁ ?_ γ₂ ?_ <;>
    refine γ.subpath_continu

Depends on / 依赖: Icc.convexComb, convexComb, subpath
-/
def subpathTransSubpathRefl (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) ((γ.subpath t₀ t₂).trans (Path.refl _)) where
  toFun x := ((γ.subpath t₀ (Icc.convexComb t₁ t₂ x.1)).trans (γ.subpath _ t₂)) x.2
  continuous_toFun := by
    let γ₁ (t : I) := γ.subpath t₀ (Icc.convexComb t₁ t₂ t)
    let γ₂ (t : I) := γ.subpath (Icc.convexComb t₁ t₂ t) t₂
    refine Path.trans_continuous_family γ₁ ?_ γ₂ ?_ <;>
    refine γ.subpath_continuous_family.comp (.prodMk ?_ <| .prodMk ?_ ?_) <;>
    fun_prop
  map_zero_left _ := by rw [Icc.convexComb_zero, coe_toContinuousMap]
  map_one_left _ := by rw [Icc.convexComb_one, subpath_self, coe_toContinuousMap]
  prop' _ _ hx := by
    rcases hx with rfl | rfl <;>
    simp

/--
Definition of `subpathTransSubpath` / `subpathTransSubpath` 的定义

English:
definition subpathTransSubpath
  signature: (γ : Path a b) (t₀ t₁ t₂ : I)
  body: trans (subpathTransSubpathRefl γ t₀ t₁ t₂) (transRefl _)

中文:
定义 subpathTransSubpath
  签名: (γ : 道路 a b) (t₀ t₁ t₂ : I)
  定义体: trans (subpathTransSubpathRefl γ t₀ t₁ t₂) (transRefl _)

Depends on / 依赖: subpathTransSubpathRefl, transRefl
-/
def subpathTransSubpath (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) (γ.subpath t₀ t₂) :=
  trans (subpathTransSubpathRefl γ t₀ t₁ t₂) (transRefl _)

end Homotopy

/-!
## Concatenation of paths
-/

variable {n : Nat}

/--
Definition of `concat` / `concat` 的定义

English:
definition concat
  signature: (p : Fin (n + 1) -> X) (F : (k : Fin n) -> Path (p k.castSucc) (p k.succ))
  body: dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

中文:
定义 concat
  签名: (p : 有限集 (n + 1) -> X) (F : (k : 有限集 n) -> 道路 (p k.castSucc) (p k.succ))
  定义体: dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

Depends on / 依赖: dfoldl, ih.trans
-/
def concat (p : Fin (n + 1) -> X) (F : (k : Fin n) -> Path (p k.castSucc) (p k.succ)) :
    Path (p 0) (p (last n)) :=
  dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

/--
lemma `concat_zero` / 引理 `concat_zero`

English:
lemma concat_zero
  given: (p : Fin 1 -> X) (F)
  proof: by
  rw [concat]; rw [dfoldl_zero]

中文:
引理 concat_zero
  条件: (p : 有限集 1 -> X) (F)
  证明: by
  rw [concat]; rw [dfoldl_zero]
-/
@[simp] lemma concat_zero (p : Fin 1 -> X) (F) :
    concat p F = refl (p 0) := by
  rw [concat]; rw [dfoldl_zero]

/--
lemma `concat_succ` / 引理 `concat_succ`

English:
lemma concat_succ
  given: (p : Fin (n + 2) -> X) (F)
  proof: by
  rw [concat]; rw [dfoldl_succ_last]
  rfl

中文:
引理 concat_succ
  条件: (p : 有限集 (n + 2) -> X) (F)
  证明: by
  rw [concat]; rw [dfoldl_succ_last]
  rfl

Depends on / 依赖: concat, dfoldl_succ_last
-/
lemma concat_succ (p : Fin (n + 2) -> X) (F) :
    concat p F = (concat (p ∘ castSucc) (fun k => (F k.castSucc))).trans (F (last n)) := by
  rw [concat]; rw [dfoldl_succ_last]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Concatenating the constant path at `x` with itself just yields the constant path at `x`. -/
@[simp]
/--
theorem `concat_refl` / 定理 `concat_refl`

English:
theorem concat_refl
  given: (n : Nat) (x : X)
  proof: by
  induction n with
  | zero => rw [concat_zero]
  | succ _ _ =>
    rw [concat_succ]
    convert! refl_trans_refl

中文:
定理 concat_refl
  条件: (n : 自然数) (x : X)
  证明: by
  induction n with
  | zero => rw [concat_zero]
  | succ _ _ =>
    rw [concat_succ]
    convert! refl_trans_refl

Depends on / 依赖: concat_succ, concat_zero, convert, refl_trans_refl
-/
theorem concat_refl (n : Nat) (x : X) :
    concat (fun (_ : Fin (n + 1)) => x) (fun _ => Path.refl x) = Path.refl x := by
  induction n with
  | zero => rw [concat_zero]
  | succ _ _ =>
    rw [concat_succ]
    convert! refl_trans_refl

namespace Homotopy

/--
Definition of `concat` / `concat` 的定义

English:
definition concat
  signature: (p : Fin (n + 1) -> X) (F G : (k : Fin n) -> Path (p k.castSucc) (p k.succ))
  body: by
  induction n with
  | zero =>
    rw [concat_zero]; rw [concat_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [concat_succ]; rw [concat_succ]
    exact hcomp (ih _ _ _ (fun k => H k.castSucc)) (H (last n))

中文:
定义 concat
  签名: (p : 有限集 (n + 1) -> X) (F G : (k : 有限集 n) -> 道路 (p k.castSucc) (p k.succ))
  定义体: by
  induction n with
  | zero =>
    rw [concat_zero]; rw [concat_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [concat_succ]; rw [concat_succ]
    exact hcomp (ih _ _ _ (fun k => H k.castSucc)) (H (last n))
-/
protected def concat (p : Fin (n + 1) -> X) (F G : (k : Fin n) -> Path (p k.castSucc) (p k.succ))
    (H : (k : Fin n) -> (F k).Homotopy (G k)) : Homotopy (concat p F) (concat p G) := by
  induction n with
  | zero =>
    rw [concat_zero]; rw [concat_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [concat_succ]; rw [concat_succ]
    exact hcomp (ih _ _ _ (fun k => H k.castSucc)) (H (last n))

/--
Definition of `concatSubpath` / `concatSubpath` 的定义

English:
definition concatSubpath
  signature: (γ : Path a b) (t : Fin (n + 1) -> I)
  body: by
  induction n with
  | zero =>
    simp only [concat_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [concat_succ]
    exact trans ((ih (t ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

中文:
定义 concatSubpath
  签名: (γ : 道路 a b) (t : 有限集 (n + 1) -> I)
  定义体: by
  induction n with
  | zero =>
    simp only [concat_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [concat_succ]
    exact trans ((ih (t ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

Depends on / 依赖: castSucc, concat_succ, concat_zero, reduceLast, subpathTransSubpath, subpath_self
-/
def concatSubpath (γ : Path a b) (t : Fin (n + 1) -> I) :
    Homotopy
      (concat (γ ∘ t) (fun k => γ.subpath (t k.castSucc) (t k.succ)))
      (γ.subpath (t 0) (t (last n))) := by
  induction n with
  | zero =>
    simp only [concat_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [concat_succ]
    exact trans ((ih (t ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

end Homotopy

namespace Homotopic

/--
theorem `concat_one` / 定理 `concat_one`

English:
theorem concat_one
  given: (p : Fin 2 -> X) (F)
  proof: by
  simpa [concat_succ] using ⟨Homotopy.reflTrans _⟩

中文:
定理 concat_one
  条件: (p : 有限集 2 -> X) (F)
  证明: by
  simpa [concat_succ] using ⟨Homotopy.reflTrans _⟩

Depends on / 依赖: Homotopy, Homotopy.reflTrans, concat_succ, reflTrans
-/
theorem concat_one (p : Fin 2 -> X) (F) :
    Homotopic (concat p F) (F 0) := by
  simpa [concat_succ] using ⟨Homotopy.reflTrans _⟩

/--
theorem `concat_two` / 定理 `concat_two`

English:
theorem concat_two
  given: (p : Fin 3 -> X) (F)
  proof: by
  simpa [concat_succ] using hcomp ⟨Homotopy.reflTrans _⟩ (refl _)

中文:
定理 concat_two
  条件: (p : 有限集 3 -> X) (F)
  证明: by
  simpa [concat_succ] using hcomp ⟨Homotopy.reflTrans _⟩ (refl _)

Depends on / 依赖: Homotopy, Homotopy.reflTrans, concat_succ, reflTrans
-/
theorem concat_two (p : Fin 3 -> X) (F) :
    Homotopic (concat p F) ((F 0).trans (F 1)) := by
  simpa [concat_succ] using hcomp ⟨Homotopy.reflTrans _⟩ (refl _)


/--
theorem `concat_hcomp` / 定理 `concat_hcomp`

English:
theorem concat_hcomp
  statement: (p : Fin (n + 1) -> X) (F G : (k : Fin n) -> Path (p k.castSucc) (p k.succ))
  proof: ⟨Homotopy.concat p F G (fun k => (h k).some)⟩

中文:
定理 concat_hcomp
  结论: (p : 有限集 (n + 1) -> X) (F G : (k : 有限集 n) -> 道路 (p k.castSucc) (p k.succ))
  证明: ⟨Homotopy.concat p F G (fun k => (h k).some)⟩

Depends on / 依赖: Homotopy, Homotopy.concat, concat
-/
theorem concat_hcomp (p : Fin (n + 1) -> X) (F G : (k : Fin n) -> Path (p k.castSucc) (p k.succ))
    (h : (k : Fin n) -> (F k).Homotopic (G k)) : Homotopic (concat p F) (concat p G) :=
  ⟨Homotopy.concat p F G (fun k => (h k).some)⟩

/-- Alternative to `Path.Homotopy.concatSubpath` in terms of `Path.Homotopic`. -/
@[simp]
/--
theorem `concat_subpath` / 定理 `concat_subpath`

English:
theorem concat_subpath
  given: (γ : Path a b) (t : Fin (n + 1) -> I)
  proof: ⟨Homotopy.concatSubpath γ t⟩

中文:
定理 concat_subpath
  条件: (γ : 道路 a b) (t : 有限集 (n + 1) -> I)
  证明: ⟨Homotopy.concatSubpath γ t⟩

Depends on / 依赖: Homotopy, Homotopy.concatSubpath, concatSubpath
-/
theorem concat_subpath (γ : Path a b) (t : Fin (n + 1) -> I) :
    Homotopic
      (concat (γ ∘ t) (fun k => γ.subpath (t k.castSucc) (t k.succ)))
      (γ.subpath (t 0) (t (last n))) :=
  ⟨Homotopy.concatSubpath γ t⟩

end Path.Homotopic

end
