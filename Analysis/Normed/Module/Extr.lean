/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Topology.Order.LocalExtr

/-!
# (Local) maximums in a normed space

In this file we prove the following lemma, see `IsMaxFilter.norm_add_sameRay`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a maximum along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `IsMaxFilter`:
`IsMaxOn`, `IsLocalMaxOn`, and `IsLocalMax`.

## Tags

local maximum, normed space
-/

public section


variable {α X E : Type*} [SeminormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace X]

section

variable {f : α -> E} {l : Filter α} {s : Set α} {c : α} {y : E}

/--
theorem `IsMaxFilter.norm_add_sameRay` / 定理 `IsMaxFilter.norm_add_sameRay`

English:
theorem IsMaxFilter.norm_add_sameRay
  given: (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay Real (f c) y)
  proof: h.mono fun x hx => by dsimp at hx ⊢; grw [hy.norm_add, norm_add_le, hx]

中文:
定理 IsMaxFilter.norm_add_sameRay
  条件: (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay 实数 (f c) y)
  证明: h.mono fun x hx => by dsimp at hx ⊢; grw [hy.norm_add, norm_add_le, hx]

Depends on / 依赖: h.mono, hy.norm_add, norm_add, norm_add_le
-/
theorem IsMaxFilter.norm_add_sameRay (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay Real (f c) y) :
    IsMaxFilter (fun x => ‖f x + y‖) l c :=
  h.mono fun x hx => by dsimp at hx ⊢; grw [hy.norm_add, norm_add_le, hx]

/--
theorem `IsMaxFilter.norm_add_self` / 定理 `IsMaxFilter.norm_add_self`

English:
theorem IsMaxFilter.norm_add_self
  given: (h : IsMaxFilter (norm ∘ f) l c)
  proof: IsMaxFilter.norm_add_sameRay h SameRay.rfl

中文:
定理 IsMaxFilter.norm_add_self
  条件: (h : IsMaxFilter (norm ∘ f) l c)
  证明: IsMaxFilter.norm_add_sameRay h SameRay.rfl

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_sameRay, SameRay, SameRay.rfl, norm_add_sameRay
-/
theorem IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) :
    IsMaxFilter (fun x => ‖f x + f c‖) l c :=
  IsMaxFilter.norm_add_sameRay h SameRay.rfl

/--
theorem `IsMaxOn.norm_add_sameRay` / 定理 `IsMaxOn.norm_add_sameRay`

English:
theorem IsMaxOn.norm_add_sameRay
  given: (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay Real (f c) y)
  proof: IsMaxFilter.norm_add_sameRay h hy

中文:
定理 IsMaxOn.norm_add_sameRay
  条件: (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay 实数 (f c) y)
  证明: IsMaxFilter.norm_add_sameRay h hy

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_sameRay, norm_add_sameRay
-/
theorem IsMaxOn.norm_add_sameRay (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay Real (f c) y) :
    IsMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy

/--
theorem `IsMaxOn.norm_add_self` / 定理 `IsMaxOn.norm_add_self`

English:
theorem IsMaxOn.norm_add_self
  given: (h : IsMaxOn (norm ∘ f) s c)
  statement: IsMaxOn (fun x => ‖f x + f c‖) s c
  proof: IsMaxFilter.norm_add_self h

中文:
定理 IsMaxOn.norm_add_self
  条件: (h : IsMaxOn (norm ∘ f) s c)
  结论: IsMaxOn (fun x => ‖f x + f c‖) s c
  证明: IsMaxFilter.norm_add_self h

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_self, norm_add_self
-/
theorem IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h

end

variable {f : X -> E} {s : Set X} {c : X} {y : E}

/--
theorem `IsLocalMaxOn.norm_add_sameRay` / 定理 `IsLocalMaxOn.norm_add_sameRay`

English:
theorem IsLocalMaxOn.norm_add_sameRay
  given: (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay Real (f c) y)
  proof: IsMaxFilter.norm_add_sameRay h hy

中文:
定理 IsLocalMaxOn.norm_add_sameRay
  条件: (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay 实数 (f c) y)
  证明: IsMaxFilter.norm_add_sameRay h hy

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_sameRay, norm_add_sameRay
-/
theorem IsLocalMaxOn.norm_add_sameRay (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay Real (f c) y) :
    IsLocalMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy

/--
theorem `IsLocalMaxOn.norm_add_self` / 定理 `IsLocalMaxOn.norm_add_self`

English:
theorem IsLocalMaxOn.norm_add_self
  given: (h : IsLocalMaxOn (norm ∘ f) s c)
  proof: IsMaxFilter.norm_add_self h

中文:
定理 IsLocalMaxOn.norm_add_self
  条件: (h : IsLocalMaxOn (norm ∘ f) s c)
  证明: IsMaxFilter.norm_add_self h

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_self, norm_add_self
-/
theorem IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) :
    IsLocalMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h

/--
theorem `IsLocalMax.norm_add_sameRay` / 定理 `IsLocalMax.norm_add_sameRay`

English:
theorem IsLocalMax.norm_add_sameRay
  given: (h : IsLocalMax (norm ∘ f) c) (hy : SameRay Real (f c) y)
  proof: IsMaxFilter.norm_add_sameRay h hy

中文:
定理 IsLocalMax.norm_add_sameRay
  条件: (h : IsLocalMax (norm ∘ f) c) (hy : SameRay 实数 (f c) y)
  证明: IsMaxFilter.norm_add_sameRay h hy

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_sameRay, norm_add_sameRay
-/
theorem IsLocalMax.norm_add_sameRay (h : IsLocalMax (norm ∘ f) c) (hy : SameRay Real (f c) y) :
    IsLocalMax (fun x => ‖f x + y‖) c :=
  IsMaxFilter.norm_add_sameRay h hy

/--
theorem `IsLocalMax.norm_add_self` / 定理 `IsLocalMax.norm_add_self`

English:
theorem IsLocalMax.norm_add_self
  given: (h : IsLocalMax (norm ∘ f) c)
  proof: IsMaxFilter.norm_add_self h

中文:
定理 IsLocalMax.norm_add_self
  条件: (h : IsLocalMax (norm ∘ f) c)
  证明: IsMaxFilter.norm_add_self h

Depends on / 依赖: IsMaxFilter, IsMaxFilter.norm_add_self, norm_add_self
-/
theorem IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) :
    IsLocalMax (fun x => ‖f x + f c‖) c :=
  IsMaxFilter.norm_add_self h
