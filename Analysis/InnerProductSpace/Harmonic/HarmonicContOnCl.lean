/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, based on code by Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Functions Harmonic on a Domain and Continuous on Its Closure

Many theorems in harmonic analysis assume that a function is harmonic on a domain and is continuous
on its closure. In this file we define a predicate `HarmonicContOnCl` that expresses this property
and prove basic facts about this predicate.
-/

public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {f f₁ f₂ : E -> F}
  {x : E} {s : Set E} {c : Real}

open Laplacian Metric Topology

namespace InnerProductSpace

/--
Definition of `HarmonicContOnCl` / `HarmonicContOnCl` 的定义

English:
structure HarmonicContOnCl
  parameters: (f : E -> F) (s : Set E)
  axioms and operations (2):
    - harmonicOnNhd : HarmonicOnNhd f s
    - continuousOn : ContinuousOn f (closure s)

中文:
结构 HarmonicContOnCl
  参数: (f : E -> F) (s : 集合 E)
  公理与运算 (2 个):
    - harmonicOnNhd : HarmonicOnNhd f s
    - continuousOn : ContinuousOn f (closure s)
-/
structure HarmonicContOnCl (f : E -> F) (s : Set E) : Prop where
  protected harmonicOnNhd : HarmonicOnNhd f s
  protected continuousOn : ContinuousOn f (closure s)

/--
theorem `HarmonicOnNhd.harmonicContOnCl` / 定理 `HarmonicOnNhd.harmonicContOnCl`

English:
theorem HarmonicOnNhd.harmonicContOnCl
  given: (h : HarmonicOnNhd f (closure s))
  proof: ⟨h.mono subset_closure, h.continuousOn⟩

中文:
定理 HarmonicOnNhd.harmonicContOnCl
  条件: (h : HarmonicOnNhd f (closure s))
  证明: ⟨h.mono subset_closure, h.continuousOn⟩

Depends on / 依赖: continuousOn, h.continuousOn, h.mono, subset_closure
-/
theorem HarmonicOnNhd.harmonicContOnCl (h : HarmonicOnNhd f (closure s)) :
    HarmonicContOnCl f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩

/--
theorem `IsClosed.harmonicContOnCl_iff` / 定理 `IsClosed.harmonicContOnCl_iff`

English:
theorem IsClosed.harmonicContOnCl_iff
  given: (hs : IsClosed s)
  proof: (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl

中文:
定理 是闭集.harmonicContOnCl_iff
  条件: (hs : 是闭集 s)
  证明: (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl
-/
theorem IsClosed.harmonicContOnCl_iff (hs : IsClosed s) :
    HarmonicContOnCl f s ↔ HarmonicOnNhd f s where
  mp := (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl

/--
theorem `harmonicContOnCl_const` / 定理 `harmonicContOnCl_const`

English:
theorem harmonicContOnCl_const
  given: {c : F}
  statement: HarmonicContOnCl (fun _ : E => c) s
  proof: ⟨harmonicOnNhd_const c, continuousOn_const⟩

中文:
定理 harmonicContOnCl_const
  条件: {c : F}
  结论: HarmonicContOnCl (fun _ : E => c) s
  证明: ⟨harmonicOnNhd_const c, continuousOn_const⟩

Depends on / 依赖: continuousOn_const, harmonicOnNhd_const
-/
theorem harmonicContOnCl_const {c : F} : HarmonicContOnCl (fun _ : E => c) s :=
  ⟨harmonicOnNhd_const c, continuousOn_const⟩

namespace HarmonicContOnCl

/--
theorem `continuousOn_ball` / 定理 `continuousOn_ball`

English:
theorem continuousOn_ball
  given: {x : E} {r : Real} (h : HarmonicContOnCl f (ball x r))
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

中文:
定理 continuousOn_ball
  条件: {x : E} {r : 实数} (h : HarmonicContOnCl f (ball x r))
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

Depends on / 依赖: closedBall_zero, closure_ball, continuousOn, continuousOn_singleton, eq_or_ne, h.continuousOn
-/
theorem continuousOn_ball {x : E} {r : Real} (h : HarmonicContOnCl f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

/--
theorem `mk_ball` / 定理 `mk_ball`

English:
theorem mk_ball
  statement: {x : E} {r : Real} (hd : HarmonicOnNhd f (ball x r))
  proof: ⟨hd, hc.mono closure_ball_subset_closedBall⟩

中文:
定理 mk_ball
  结论: {x : E} {r : 实数} (hd : HarmonicOnNhd f (ball x r))
  证明: ⟨hd, hc.mono closure_ball_subset_closedBall⟩

Depends on / 依赖: closure_ball_subset_closedBall, hc.mono
-/
theorem mk_ball {x : E} {r : Real} (hd : HarmonicOnNhd f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) :
    HarmonicContOnCl f (ball x r) :=
⟨hd, hc.mono closure_ball_subset_closedBall⟩

/--
theorem `contDiffAt` / 定理 `contDiffAt`

English:
theorem contDiffAt
  given: (h : HarmonicContOnCl f s) (hx : x in s)
  proof: (h.1 x hx).1

中文:
定理 contDiffAt
  条件: (h : HarmonicContOnCl f s) (hx : x in s)
  证明: (h.1 x hx).1
-/
theorem contDiffAt (h : HarmonicContOnCl f s) (hx : x in s) :
    ContDiffAt Real 2 f x := (h.1 x hx).1

/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  given: (h : HarmonicContOnCl f s) (hx : x in s)
  proof: (h.contDiffAt hx).differentiableAt two_ne_zero

中文:
定理 differentiableAt
  条件: (h : HarmonicContOnCl f s) (hx : x in s)
  证明: (h.contDiffAt hx).differentiableAt two_ne_zero

Depends on / 依赖: contDiffAt, differentiableAt, h.contDiffAt, two_ne_zero
-/
theorem differentiableAt (h : HarmonicContOnCl f s) (hx : x in s) :
    DifferentiableAt Real f x := (h.contDiffAt hx).differentiableAt two_ne_zero

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {t : Set E} (h : HarmonicContOnCl f s) (ht : t subseteq s)
  proof: ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩

中文:
定理 mono
  条件: {t : 集合 E} (h : HarmonicContOnCl f s) (ht : t subseteq s)
  证明: ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩

Depends on / 依赖: closure_mono, continuousOn, h.continuousOn.mono, h.harmonicOnNhd.mono, harmonicOnNhd
-/
theorem mono {t : Set E} (h : HarmonicContOnCl f s) (ht : t subseteq s) :
    HarmonicContOnCl f t := ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s)
  proof: ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩

中文:
定理 add
  条件: (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s)
  证明: ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩
-/
@[to_fun] theorem add (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ + f₂) s := ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩

/--
theorem `add_const` / 定理 `add_const`

English:
theorem add_const
  given: (hf : HarmonicContOnCl f s) (c : F)
  proof: hf.add harmonicContOnCl_const

中文:
定理 add_const
  条件: (hf : HarmonicContOnCl f s) (c : F)
  证明: hf.add harmonicContOnCl_const
-/
@[to_fun] theorem add_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f + fun _ => c) s := hf.add harmonicContOnCl_const

/--
theorem `const_add` / 定理 `const_add`

English:
theorem const_add
  given: (hf : HarmonicContOnCl f s) (c : F)
  proof: harmonicContOnCl_const.add hf

中文:
定理 const_add
  条件: (hf : HarmonicContOnCl f s) (c : F)
  证明: harmonicContOnCl_const.add hf
-/
@[to_fun] theorem const_add (hf : HarmonicContOnCl f s) (c : F) :
  HarmonicContOnCl ((fun _ => c) + f) s := harmonicContOnCl_const.add hf

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : HarmonicContOnCl f s)
  proof: ⟨hf.1.neg, hf.2.neg⟩

中文:
定理 neg
  条件: (hf : HarmonicContOnCl f s)
  证明: ⟨hf.1.neg, hf.2.neg⟩
-/
@[to_fun] theorem neg (hf : HarmonicContOnCl f s) :
    HarmonicContOnCl (-f) s := ⟨hf.1.neg, hf.2.neg⟩

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s)
  proof: ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩

中文:
定理 sub
  条件: (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s)
  证明: ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩
-/
@[to_fun] theorem sub (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ - f₂) s := ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩

/--
theorem `sub_const` / 定理 `sub_const`

English:
theorem sub_const
  given: (hf : HarmonicContOnCl f s) (c : F)
  proof: hf.sub harmonicContOnCl_const

中文:
定理 sub_const
  条件: (hf : HarmonicContOnCl f s) (c : F)
  证明: hf.sub harmonicContOnCl_const
-/
@[to_fun] theorem sub_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f - fun _ => c) s := hf.sub harmonicContOnCl_const

/--
theorem `const_sub` / 定理 `const_sub`

English:
theorem const_sub
  given: (hf : HarmonicContOnCl f s) (c : F)
  proof: harmonicContOnCl_const.sub hf

中文:
定理 const_sub
  条件: (hf : HarmonicContOnCl f s) (c : F)
  证明: harmonicContOnCl_const.sub hf
-/
@[to_fun] theorem const_sub (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl ((fun _ => c) - f) s := harmonicContOnCl_const.sub hf

/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  given: (hf : HarmonicContOnCl f s) (c : Real)
  proof: ⟨hf.1.const_smul, hf.2.const_smul c⟩

中文:
定理 const_smul
  条件: (hf : HarmonicContOnCl f s) (c : 实数)
  证明: ⟨hf.1.const_smul, hf.2.const_smul c⟩
-/
@[to_fun] theorem const_smul (hf : HarmonicContOnCl f s) (c : Real) :
    HarmonicContOnCl (c • f) s := ⟨hf.1.const_smul, hf.2.const_smul c⟩

end HarmonicContOnCl

end InnerProductSpace
