/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Vector fields in vector spaces

We study functions of the form `V : E → E` on a vector space, thinking of these as vector fields.
We define several notions in this context, with the aim to generalize them to vector fields on
manifolds.

Notably, we define the pullback of a vector field under a map, as
`VectorField.pullback 𝕜 f V x := (fderiv 𝕜 f x).inverse (V (f x))` (together with the same notion
within a set).

We also define the Lie bracket of two vector fields as
`VectorField.lieBracket 𝕜 V W x := fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)`
(together with the same notion within a set).

In addition to comprehensive API on these two notions, the main results are the following:
* `VectorField.pullback_lieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks, when the second derivative is symmetric.
* `VectorField.leibniz_identity_lieBracket` is the Leibniz
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

@[expose] public section

open Set
open scoped Topology ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E -> E} {s t : Set E} {x : E}

/-!
### The Lie bracket of vector fields in a vector space

We define the Lie bracket of two vector fields, and call it `lieBracket 𝕜 V W x`. We also define
a version localized to sets, `lieBracketWithin 𝕜 V W s x`. We copy the relevant API
of `fderivWithin` and `fderiv` for these notions to get a comprehensive API.
-/

namespace VectorField

variable (𝕜) in
/--
Definition of `lieBracket` / `lieBracket` 的定义

English:
definition lieBracket
  signature: (V W : E -> E) (x : E)
  body: fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

中文:
定义 lieBracket
  签名: (V W : E -> E) (x : E)
  定义体: fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

Depends on / 依赖: fderiv
-/
def lieBracket (V W : E -> E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

variable (𝕜) in
/--
Definition of `lieBracketWithin` / `lieBracketWithin` 的定义

English:
definition lieBracketWithin
  signature: (V W : E -> E) (s : Set E) (x : E)
  body: fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

中文:
定义 lieBracketWithin
  签名: (V W : E -> E) (s : 集合 E) (x : E)
  定义体: fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

Depends on / 依赖: fderivWithin
-/
def lieBracketWithin (V W : E -> E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

/--
lemma `lieBracket_eq` / 引理 `lieBracket_eq`

English:
lemma lieBracket_eq
  proof: rfl

中文:
引理 lieBracket_eq
  证明: rfl
-/
lemma lieBracket_eq :
    lieBracket 𝕜 V W = fun x => fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl

/--
lemma `lieBracketWithin_eq` / 引理 `lieBracketWithin_eq`

English:
lemma lieBracketWithin_eq
  proof: rfl

@[simp]

中文:
引理 lieBracketWithin_eq
  证明: rfl

@[simp]
-/
lemma lieBracketWithin_eq :
    lieBracketWithin 𝕜 V W s =
      fun x => fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x) := rfl

@[simp]
/--
theorem `lieBracketWithin_univ` / 定理 `lieBracketWithin_univ`

English:
theorem lieBracketWithin_univ
  statement: lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W
  proof: by
  ext1 x
  simp [lieBracketWithin, lieBracket]

中文:
定理 lieBracketWithin_univ
  结论: lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W
  证明: by
  ext1 x
  simp [lieBracketWithin, lieBracket]

Depends on / 依赖: lieBracket, lieBracketWithin
-/
theorem lieBracketWithin_univ : lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W := by
  ext1 x
  simp [lieBracketWithin, lieBracket]

/--
lemma `lieBracketWithin_eq_zero_of_eq_zero` / 引理 `lieBracketWithin_eq_zero_of_eq_zero`

English:
lemma lieBracketWithin_eq_zero_of_eq_zero
  given: (hV : V x = 0) (hW : W x = 0)
  proof: by
  simp [lieBracketWithin, hV, hW]

中文:
引理 lieBracketWithin_eq_zero_of_eq_zero
  条件: (hV : V x = 0) (hW : W x = 0)
  证明: by
  simp [lieBracketWithin, hV, hW]

Depends on / 依赖: lieBracketWithin
-/
lemma lieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracketWithin 𝕜 V W s x = 0 := by
  simp [lieBracketWithin, hV, hW]

/--
lemma `lieBracket_eq_zero_of_eq_zero` / 引理 `lieBracket_eq_zero_of_eq_zero`

English:
lemma lieBracket_eq_zero_of_eq_zero
  given: (hV : V x = 0) (hW : W x = 0)
  proof: by
  simp [lieBracket, hV, hW]

中文:
引理 lieBracket_eq_zero_of_eq_zero
  条件: (hV : V x = 0) (hW : W x = 0)
  证明: by
  simp [lieBracket, hV, hW]

Depends on / 依赖: lieBracket
-/
lemma lieBracket_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracket 𝕜 V W x = 0 := by
  simp [lieBracket, hV, hW]

/--
lemma `lieBracketWithin_swap` / 引理 `lieBracketWithin_swap`

English:
lemma lieBracketWithin_swap
  statement: lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s
  proof: by
  ext x; simp [lieBracketWithin]

中文:
引理 lieBracketWithin_swap
  结论: lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s
  证明: by
  ext x; simp [lieBracketWithin]

Depends on / 依赖: lieBracketWithin
-/
lemma lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s := by
  ext x; simp [lieBracketWithin]

/--
lemma `lieBracket_swap` / 引理 `lieBracket_swap`

English:
lemma lieBracket_swap
  statement: lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x
  proof: by
  simp [lieBracket]

中文:
引理 lieBracket_swap
  结论: lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x
  证明: by
  simp [lieBracket]

Depends on / 依赖: lieBracket
-/
lemma lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x := by
  simp [lieBracket]

/--
lemma `lieBracketWithin_self` / 引理 `lieBracketWithin_self`

English:
lemma lieBracketWithin_self
  statement: lieBracketWithin 𝕜 V V s = 0
  proof: by
  ext x; simp [lieBracketWithin]

中文:
引理 lieBracketWithin_self
  结论: lieBracketWithin 𝕜 V V s = 0
  证明: by
  ext x; simp [lieBracketWithin]
-/
@[simp] lemma lieBracketWithin_self : lieBracketWithin 𝕜 V V s = 0 := by
  ext x; simp [lieBracketWithin]

/--
lemma `lieBracket_self` / 引理 `lieBracket_self`

English:
lemma lieBracket_self
  statement: lieBracket 𝕜 V V = 0
  proof: by
  ext x; simp [lieBracket]

中文:
引理 lieBracket_self
  结论: lieBracket 𝕜 V V = 0
  证明: by
  ext x; simp [lieBracket]
-/
@[simp] lemma lieBracket_self : lieBracket 𝕜 V V = 0 := by
  ext x; simp [lieBracket]

/--
lemma `lieBracketWithin_const_smul_left` / 引理 `lieBracketWithin_const_smul_left`

English:
lemma lieBracketWithin_const_smul_left
  statement: {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x)
  proof: by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hV]

中文:
引理 lieBracketWithin_const_smul_left
  结论: {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x)
  证明: by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hV]

Depends on / 依赖: fderivWithin_const_smul, lieBracketWithin, smul_sub
-/
lemma lieBracketWithin_const_smul_left {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (c • V) W s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hV]

/--
lemma `lieBracket_const_smul_left` / 引理 `lieBracket_const_smul_left`

English:
lemma lieBracket_const_smul_left
  given: {c : 𝕜} (hV : DifferentiableAt 𝕜 V x)
  proof: by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hV ⊢
  exact lieBracketWithin_const_smul_left hV uniqueDiffWithinAt_univ

中文:
引理 lieBracket_const_smul_left
  条件: {c : 𝕜} (hV : DifferentiableAt 𝕜 V x)
  证明: by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hV ⊢
  exact lieBracketWithin_const_smul_left hV uniqueDiffWithinAt_univ

Depends on / 依赖: differentiableWithinAt_univ, lieBracketWithin_const_smul_left, lieBracketWithin_univ, uniqueDiffWithinAt_univ
-/
lemma lieBracket_const_smul_left {c : 𝕜} (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (c • V) W x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hV ⊢
  exact lieBracketWithin_const_smul_left hV uniqueDiffWithinAt_univ

/--
lemma `lieBracketWithin_const_smul_right` / 引理 `lieBracketWithin_const_smul_right`

English:
lemma lieBracketWithin_const_smul_right
  statement: {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x)
  proof: by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hW]

中文:
引理 lieBracketWithin_const_smul_right
  结论: {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x)
  证明: by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hW]

Depends on / 依赖: fderivWithin_const_smul, lieBracketWithin, smul_sub
-/
lemma lieBracketWithin_const_smul_right {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (c • W) s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hW]

/--
lemma `lieBracket_const_smul_right` / 引理 `lieBracket_const_smul_right`

English:
lemma lieBracket_const_smul_right
  given: {c : 𝕜} (hW : DifferentiableAt 𝕜 W x)
  proof: by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  exact lieBracketWithin_const_smul_right hW uniqueDiffWithinAt_univ

中文:
引理 lieBracket_const_smul_right
  条件: {c : 𝕜} (hW : DifferentiableAt 𝕜 W x)
  证明: by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  exact lieBracketWithin_const_smul_right hW uniqueDiffWithinAt_univ

Depends on / 依赖: differentiableWithinAt_univ, lieBracketWithin_const_smul_right, lieBracketWithin_univ, uniqueDiffWithinAt_univ
-/
lemma lieBracket_const_smul_right {c : 𝕜} (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (c • W) x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  exact lieBracketWithin_const_smul_right hW uniqueDiffWithinAt_univ

/--
lemma `lieBracketWithin_smul_right` / 引理 `lieBracketWithin_smul_right`

English:
lemma lieBracketWithin_smul_right
  statement: {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  simp [lieBracketWithin, fderivWithin_fun_smul hs hf hW, map_smul, add_comm, smul_sub,
    add_sub_assoc]

中文:
引理 lieBracketWithin_smul_right
  结论: {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  simp [lieBracketWithin, fderivWithin_fun_smul hs hf hW, map_smul, add_comm, smul_sub,
    add_sub_assoc]

Depends on / 依赖: add_comm, add_sub_assoc, fderivWithin_fun_smul, lieBracketWithin, map_smul, smul_sub
-/
lemma lieBracketWithin_smul_right {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (fun y => f y • W y) s x =
      (fderivWithin 𝕜 f s x) (V x) • (W x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_fun_smul hs hf hW, map_smul, add_comm, smul_sub,
    add_sub_assoc]

/--
lemma `lieBracket_smul_right` / 引理 `lieBracket_smul_right`

English:
lemma lieBracket_smul_right
  statement: {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
  proof: by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

中文:
引理 lieBracket_smul_right
  结论: {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
  证明: by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

Depends on / 依赖: differentiableWithinAt_univ, fderiv, lieBracketWithin_smul_right, lieBracketWithin_univ, simp_rw, uniqueDiffWithinAt_univ
-/
lemma lieBracket_smul_right {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (fun y => f y • W y) x =
      (fderiv 𝕜 f x) (V x) • (W x) + (f x) • lieBracket 𝕜 V W x := by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

/--
lemma `lieBracketWithin_smul_left` / 引理 `lieBracketWithin_smul_left`

English:
lemma lieBracketWithin_smul_left
  statement: {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  rw [lieBracketWithin_swap]; rw [Pi.neg_apply]; rw [lieBracketWithin_smul_right hf hV hs]; rw [lieBracketWithin_swap]; rw [add_comm]
  simp

中文:
引理 lieBracketWithin_smul_left
  结论: {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  rw [lieBracketWithin_swap]; rw [Pi.neg_apply]; rw [lieBracketWithin_smul_right hf hV hs]; rw [lieBracketWithin_swap]; rw [add_comm]
  simp

Depends on / 依赖: Pi.neg_apply, add_comm, lieBracketWithin_smul_right, lieBracketWithin_swap, neg_apply
-/
lemma lieBracketWithin_smul_left {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hV : DifferentiableWithinAt 𝕜 V s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (fun y => f y • V y) W s x =
      - (fderivWithin 𝕜 f s x) (W x) • (V x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  rw [lieBracketWithin_swap]; rw [Pi.neg_apply]; rw [lieBracketWithin_smul_right hf hV hs]; rw [lieBracketWithin_swap]; rw [add_comm]
  simp

/--
lemma `lieBracket_smul_left` / 引理 `lieBracket_smul_left`

English:
lemma lieBracket_smul_left
  statement: {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
  proof: by
  rw [lieBracket_swap]; rw [lieBracket_smul_right hf hV]; rw [lieBracket_swap]; rw [add_comm]
  simp

中文:
引理 lieBracket_smul_left
  结论: {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
  证明: by
  rw [lieBracket_swap]; rw [lieBracket_smul_right hf hV]; rw [lieBracket_swap]; rw [add_comm]
  simp

Depends on / 依赖: add_comm, lieBracket_smul_right, lieBracket_swap
-/
lemma lieBracket_smul_left {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (fun y => f y • V y) W x =
      - (fderiv 𝕜 f x) (W x) • (V x) + (f x) • lieBracket 𝕜 V W x := by
  rw [lieBracket_swap]; rw [lieBracket_smul_right hf hV]; rw [lieBracket_swap]; rw [add_comm]
  simp

/--
lemma `lieBracketWithin_add_left` / 引理 `lieBracketWithin_add_left`

English:
lemma lieBracketWithin_add_left
  statement: (hV : DifferentiableWithinAt 𝕜 V s x)
  proof: by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hV hV₁]; rw [add_apply]
  abel

中文:
引理 lieBracketWithin_add_left
  结论: (hV : DifferentiableWithinAt 𝕜 V s x)
  证明: by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hV hV₁]; rw [add_apply]
  abel

Depends on / 依赖: Pi.add_apply, add_apply, fderivWithin_add, lieBracketWithin, map_add
-/
lemma lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x)
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (V + V₁) W s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hV hV₁]; rw [add_apply]
  abel

/--
lemma `lieBracket_add_left` / 引理 `lieBracket_add_left`

English:
lemma lieBracket_add_left
  given: (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x)
  proof: by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hV hV₁]; rw [add_apply]
  abel

中文:
引理 lieBracket_add_left
  条件: (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x)
  证明: by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hV hV₁]; rw [add_apply]
  abel

Depends on / 依赖: Pi.add_apply, add_apply, fderiv_add, lieBracket, map_add
-/
lemma lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x) :
    lieBracket 𝕜 (V + V₁) W x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hV hV₁]; rw [add_apply]
  abel

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
/--
lemma `lieBracketWithin_zero_left` / 引理 `lieBracketWithin_zero_left`

English:
lemma lieBracketWithin_zero_left
  statement: lieBracketWithin 𝕜 0 W s = 0
  proof: by ext; simp [lieBracketWithin]

中文:
引理 lieBracketWithin_zero_left
  结论: lieBracketWithin 𝕜 0 W s = 0
  证明: by ext; simp [lieBracketWithin]

Depends on / 依赖: lieBracketWithin
-/
lemma lieBracketWithin_zero_left : lieBracketWithin 𝕜 0 W s = 0 := by ext; simp [lieBracketWithin]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
/--
lemma `lieBracketWithin_zero_right` / 引理 `lieBracketWithin_zero_right`

English:
lemma lieBracketWithin_zero_right
  statement: lieBracketWithin 𝕜 W 0 s = 0
  proof: by ext; simp [lieBracketWithin]

中文:
引理 lieBracketWithin_zero_right
  结论: lieBracketWithin 𝕜 W 0 s = 0
  证明: by ext; simp [lieBracketWithin]

Depends on / 依赖: lieBracketWithin
-/
lemma lieBracketWithin_zero_right : lieBracketWithin 𝕜 W 0 s = 0 := by ext; simp [lieBracketWithin]

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
/--
lemma `lieBracket_zero_left` / 引理 `lieBracket_zero_left`

English:
lemma lieBracket_zero_left
  statement: lieBracket 𝕜 0 W = 0
  proof: by simp [← lieBracketWithin_univ]

中文:
引理 lieBracket_zero_left
  结论: lieBracket 𝕜 0 W = 0
  证明: by simp [← lieBracketWithin_univ]

Depends on / 依赖: lieBracketWithin_univ
-/
lemma lieBracket_zero_left : lieBracket 𝕜 0 W = 0 := by simp [← lieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
/--
lemma `lieBracket_zero_right` / 引理 `lieBracket_zero_right`

English:
lemma lieBracket_zero_right
  statement: lieBracket 𝕜 W 0 = 0
  proof: by simp [← lieBracketWithin_univ]

中文:
引理 lieBracket_zero_right
  结论: lieBracket 𝕜 W 0 = 0
  证明: by simp [← lieBracketWithin_univ]

Depends on / 依赖: lieBracketWithin_univ
-/
lemma lieBracket_zero_right : lieBracket 𝕜 W 0 = 0 := by simp [← lieBracketWithin_univ]

/--
lemma `lieBracketWithin_add_right` / 引理 `lieBracketWithin_add_right`

English:
lemma lieBracketWithin_add_right
  statement: (hW : DifferentiableWithinAt 𝕜 W s x)
  proof: by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hW hW₁]; rw [add_apply]
  abel

中文:
引理 lieBracketWithin_add_right
  结论: (hW : DifferentiableWithinAt 𝕜 W s x)
  证明: by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hW hW₁]; rw [add_apply]
  abel

Depends on / 依赖: Pi.add_apply, add_apply, fderivWithin_add, lieBracketWithin, map_add
-/
lemma lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (W + W₁) s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hW hW₁]; rw [add_apply]
  abel

/--
lemma `lieBracket_add_right` / 引理 `lieBracket_add_right`

English:
lemma lieBracket_add_right
  given: (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x)
  proof: by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hW hW₁]; rw [add_apply]
  abel

中文:
引理 lieBracket_add_right
  条件: (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x)
  证明: by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hW hW₁]; rw [add_apply]
  abel

Depends on / 依赖: Pi.add_apply, add_apply, fderiv_add, lieBracket, map_add
-/
lemma lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x) :
    lieBracket 𝕜 V (W + W₁) x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hW hW₁]; rw [add_apply]
  abel

/--
lemma `fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt` / 引理 `fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt`

English:
lemma fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt
  statement: {f : E -> F}
  proof: by
  have H₀ : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (by decide) hxs).differentiableWithinAt one_ne_zero
  have H₁ : UniqueDiffWithinAt 𝕜 s x := hs x hxs
  rw [fderivWithin_clm_apply]; rw [fderivWithin_clm_apply] <;> try assumption
  simp [lieBracketWithi

中文:
引理 fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt
  结论: {f : E -> F}
  证明: by
  have H₀ : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (by decide) hxs).differentiableWithinAt one_ne_zero
  have H₁ : UniqueDiffWithinAt 𝕜 s x := hs x hxs
  rw [fderivWithin_clm_apply]; rw [fderivWithin_clm_apply] <;> try assumption
  simp [lieBracketWithi

Depends on / 依赖: DifferentiableWithinAt, UniqueDiffWithinAt, differentiableWithinAt, fderivWithin, fderivWithin_clm_apply, fderivWithin_right, hf.fderivWithin_right, lieBracketWithin, one_ne_zero
-/
lemma fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt {f : E -> F}
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hsymm : IsSymmSndFDerivWithinAt 𝕜 f s x)
    (hs : UniqueDiffOn 𝕜 s) (hxs : x in s)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    fderivWithin 𝕜 f s x (lieBracketWithin 𝕜 V W s x) =
      fderivWithin 𝕜 (fun x => fderivWithin 𝕜 f s x (W x)) s x (V x) -
        fderivWithin 𝕜 (fun x => fderivWithin 𝕜 f s x (V x)) s x (W x) := by
  have H₀ : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (by decide) hxs).differentiableWithinAt one_ne_zero
  have H₁ : UniqueDiffWithinAt 𝕜 s x := hs x hxs
  rw [fderivWithin_clm_apply]; rw [fderivWithin_clm_apply] <;> try assumption
  simp [lieBracketWithin, hsymm (V _) (W _)]

/--
lemma `fderiv_apply_lieBracket_of_isSymmSndFDerivAt` / 引理 `fderiv_apply_lieBracket_of_isSymmSndFDerivAt`

English:
lemma fderiv_apply_lieBracket_of_isSymmSndFDerivAt
  statement: {f : E -> F}
  proof: by
  simp only [← fderivWithin_univ, ← lieBracketWithin_univ, ← contDiffWithinAt_univ,
    ← isSymmSndFDerivWithinAt_univ, ← differentiableWithinAt_univ] at *
  exact fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt hf hsymm (by simp) (by simp)
    hW hV

中文:
引理 fderiv_apply_lieBracket_of_isSymmSndFDerivAt
  结论: {f : E -> F}
  证明: by
  simp only [← fderivWithin_univ, ← lieBracketWithin_univ, ← contDiffWithinAt_univ,
    ← isSymmSndFDerivWithinAt_univ, ← differentiableWithinAt_univ] at *
  exact fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt hf hsymm (by simp) (by simp)
    hW hV

Depends on / 依赖: contDiffWithinAt_univ, differentiableWithinAt_univ, fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt, fderivWithin_univ, isSymmSndFDerivWithinAt_univ, lieBracketWithin_univ
-/
lemma fderiv_apply_lieBracket_of_isSymmSndFDerivAt {f : E -> F}
    (hf : ContDiffAt 𝕜 2 f x) (hsymm : IsSymmSndFDerivAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) (hV : DifferentiableAt 𝕜 V x) :
    fderiv 𝕜 f x (lieBracket 𝕜 V W x) =
      fderiv 𝕜 (fun x => fderiv 𝕜 f x (W x)) x (V x) -
        fderiv 𝕜 (fun x => fderiv 𝕜 f x (V x)) x (W x) := by
  simp only [← fderivWithin_univ, ← lieBracketWithin_univ, ← contDiffWithinAt_univ,
    ← isSymmSndFDerivWithinAt_univ, ← differentiableWithinAt_univ] at *
  exact fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt hf hsymm (by simp) (by simp)
    hW hV

/--
lemma `fderivWithin_apply_lieBracket` / 引理 `fderivWithin_apply_lieBracket`

English:
lemma fderivWithin_apply_lieBracket
  statement: {f : E -> F} {n : Nat∞ω}
  proof: by
  apply fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivWithinAt hn hs hxs' hxs]

中文:
引理 fderivWithin_apply_lieBracket
  结论: {f : E -> F} {n : 自然数∞ω}
  证明: by
  apply fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivWithinAt hn hs hxs' hxs]

Depends on / 依赖: exacts, fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt, hf.isSymmSndFDerivWithinAt, hf.of_le, isSymmSndFDerivWithinAt, le_minSmoothness, le_minSmoothness.trans, of_le
-/
lemma fderivWithin_apply_lieBracket {f : E -> F} {n : Nat∞ω}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2 <= n)
    (hs : UniqueDiffOn 𝕜 s) (hxs' : x in closure (interior s)) (hxs : x in s)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    fderivWithin 𝕜 f s x (lieBracketWithin 𝕜 V W s x) =
      fderivWithin 𝕜 (fun x => fderivWithin 𝕜 f s x (W x)) s x (V x) -
        fderivWithin 𝕜 (fun x => fderivWithin 𝕜 f s x (V x)) s x (W x) := by
  apply fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivWithinAt hn hs hxs' hxs]

/--
lemma `fderiv_apply_lieBracket` / 引理 `fderiv_apply_lieBracket`

English:
lemma fderiv_apply_lieBracket
  statement: {f : E -> F} {n : Nat∞ω}
  proof: by
  apply fderiv_apply_lieBracket_of_isSymmSndFDerivAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivAt hn]

中文:
引理 fderiv_apply_lieBracket
  结论: {f : E -> F} {n : 自然数∞ω}
  证明: by
  apply fderiv_apply_lieBracket_of_isSymmSndFDerivAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivAt hn]

Depends on / 依赖: exacts, fderiv_apply_lieBracket_of_isSymmSndFDerivAt, hf.isSymmSndFDerivAt, hf.of_le, isSymmSndFDerivAt, le_minSmoothness, le_minSmoothness.trans, of_le
-/
lemma fderiv_apply_lieBracket {f : E -> F} {n : Nat∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 <= n)
    (hW : DifferentiableAt 𝕜 W x) (hV : DifferentiableAt 𝕜 V x) :
    fderiv 𝕜 f x (lieBracket 𝕜 V W x) =
      fderiv 𝕜 (fun x => fderiv 𝕜 f x (W x)) x (V x) -
        fderiv 𝕜 (fun x => fderiv 𝕜 f x (V x)) x (W x) := by
  apply fderiv_apply_lieBracket_of_isSymmSndFDerivAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivAt hn]

/--
lemma `_root_.ContDiffWithinAt.lieBracketWithin_vectorField` / 引理 `_root_.ContDiffWithinAt.lieBracketWithin_vectorField`

English:
lemma _root_.ContDiffWithinAt.lieBracketWithin_vectorField
  proof: by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

中文:
引理 _root_.ContDiffWithinAt.lieBracketWithin_vectorField
  证明: by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.clm_apply, ContDiffWithinAt.sub, clm_apply, fderivWithin_right, hV.fderivWithin_right, hV.of_le, hW.fderivWithin_right, hW.of_le, le_self_add, le_trans, of_le
-/
lemma _root_.ContDiffWithinAt.lieBracketWithin_vectorField
    {m n : Nat∞ω} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (hx : x in s) :
    ContDiffWithinAt 𝕜 m (lieBracketWithin 𝕜 V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

/--
lemma `_root_.ContDiffAt.lieBracket_vectorField` / 引理 `_root_.ContDiffAt.lieBracket_vectorField`

English:
lemma _root_.ContDiffAt.lieBracket_vectorField
  statement: {m n : Nat∞ω} (hV : ContDiffAt 𝕜 n V x)
  proof: by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)

中文:
引理 _root_.ContDiffAt.lieBracket_vectorField
  结论: {m n : 自然数∞ω} (hV : ContDiffAt 𝕜 n V x)
  证明: by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)

Depends on / 依赖: contDiffWithinAt_univ, hV.lieBracketWithin_vectorField, lieBracketWithin_univ, lieBracketWithin_vectorField, mem_univ, simp_rw, uniqueDiffOn_univ
-/
lemma _root_.ContDiffAt.lieBracket_vectorField {m n : Nat∞ω} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 <= n) :
    ContDiffAt 𝕜 m (lieBracket 𝕜 V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)

/--
lemma `_root_.ContDiffOn.lieBracketWithin_vectorField` / 引理 `_root_.ContDiffOn.lieBracketWithin_vectorField`

English:
lemma _root_.ContDiffOn.lieBracketWithin_vectorField
  statement: {m n : Nat∞ω} (hV : ContDiffOn 𝕜 n V s)
  proof: fun x hx => (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx

中文:
引理 _root_.ContDiffOn.lieBracketWithin_vectorField
  结论: {m n : 自然数∞ω} (hV : ContDiffOn 𝕜 n V s)
  证明: fun x hx => (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx

Depends on / 依赖: lieBracketWithin_vectorField
-/
lemma _root_.ContDiffOn.lieBracketWithin_vectorField {m n : Nat∞ω} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) :
    ContDiffOn 𝕜 m (lieBracketWithin 𝕜 V W s) s :=
  fun x hx => (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx

/--
lemma `_root_.ContDiff.lieBracket_vectorField` / 引理 `_root_.ContDiff.lieBracket_vectorField`

English:
lemma _root_.ContDiff.lieBracket_vectorField
  statement: {m n : Nat∞ω} (hV : ContDiff 𝕜 n V)
  proof: contDiff_iff_contDiffAt.2 (fun _ => hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)

中文:
引理 _root_.连续可微.lieBracket_vectorField
  结论: {m n : 自然数∞ω} (hV : 连续可微 𝕜 n V)
  证明: contDiff_iff_contDiffAt.2 (fun _ => hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hV.contDiffAt.lieBracket_vectorField, hW.contDiffAt, lieBracket_vectorField
-/
lemma _root_.ContDiff.lieBracket_vectorField {m n : Nat∞ω} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 <= n) :
    ContDiff 𝕜 m (lieBracket 𝕜 V W) :=
  contDiff_iff_contDiffAt.2 (fun _ => hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)

/--
theorem `lieBracketWithin_of_mem_nhdsWithin` / 定理 `lieBracketWithin_of_mem_nhdsWithin`

English:
theorem lieBracketWithin_of_mem_nhdsWithin
  statement: (st : t in 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp [lieBracketWithin, fderivWithin_of_mem_nhdsWithin st hs hV,
    fderivWithin_of_mem_nhdsWithin st hs hW]

中文:
定理 lieBracketWithin_of_mem_nhdsWithin
  结论: (st : t in 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp [lieBracketWithin, fderivWithin_of_mem_nhdsWithin st hs hV,
    fderivWithin_of_mem_nhdsWithin st hs hW]

Depends on / 依赖: fderivWithin_of_mem_nhdsWithin, lieBracketWithin
-/
theorem lieBracketWithin_of_mem_nhdsWithin (st : t in 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_of_mem_nhdsWithin st hs hV,
    fderivWithin_of_mem_nhdsWithin st hs hW]

/--
theorem `lieBracketWithin_subset` / 定理 `lieBracketWithin_subset`

English:
theorem lieBracketWithin_subset
  statement: (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
  proof: lieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

中文:
定理 lieBracketWithin_subset
  结论: (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
  证明: lieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

Depends on / 依赖: lieBracketWithin_of_mem_nhdsWithin, nhdsWithin_mono, self_mem_nhdsWithin
-/
theorem lieBracketWithin_subset (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

/--
theorem `lieBracketWithin_inter` / 定理 `lieBracketWithin_inter`

English:
theorem lieBracketWithin_inter
  given: (ht : t in 𝓝 x)
  proof: by
  simp [lieBracketWithin, fderivWithin_inter, ht]

中文:
定理 lieBracketWithin_inter
  条件: (ht : t in 𝓝 x)
  证明: by
  simp [lieBracketWithin, fderivWithin_inter, ht]

Depends on / 依赖: fderivWithin_inter, lieBracketWithin
-/
theorem lieBracketWithin_inter (ht : t in 𝓝 x) :
    lieBracketWithin 𝕜 V W (s inter t) x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_inter, ht]

/--
theorem `lieBracketWithin_of_mem_nhds` / 定理 `lieBracketWithin_of_mem_nhds`

English:
theorem lieBracketWithin_of_mem_nhds
  given: (h : s in 𝓝 x)
  proof: by
  rw [← lieBracketWithin_univ]; rw [← univ_inter s]; rw [lieBracketWithin_inter h]

中文:
定理 lieBracketWithin_of_mem_nhds
  条件: (h : s in 𝓝 x)
  证明: by
  rw [← lieBracketWithin_univ]; rw [← univ_inter s]; rw [lieBracketWithin_inter h]

Depends on / 依赖: lieBracketWithin_inter, lieBracketWithin_univ, univ_inter
-/
theorem lieBracketWithin_of_mem_nhds (h : s in 𝓝 x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ]; rw [← univ_inter s]; rw [lieBracketWithin_inter h]

/--
theorem `lieBracketWithin_of_isOpen` / 定理 `lieBracketWithin_of_isOpen`

English:
theorem lieBracketWithin_of_isOpen
  given: (hs : IsOpen s) (hx : x in s)
  proof: lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

中文:
定理 lieBracketWithin_of_isOpen
  条件: (hs : 是开集 s) (hx : x in s)
  证明: lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

Depends on / 依赖: hs.mem_nhds, lieBracketWithin_of_mem_nhds, mem_nhds
-/
theorem lieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x in s) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x :=
  lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

/--
theorem `lieBracketWithin_eq_lieBracket` / 定理 `lieBracketWithin_eq_lieBracket`

English:
theorem lieBracketWithin_eq_lieBracket
  statement: (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

中文:
定理 lieBracketWithin_eq_lieBracket
  结论: (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

Depends on / 依赖: fderivWithin_eq_fderiv, lieBracket, lieBracketWithin
-/
theorem lieBracketWithin_eq_lieBracket (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

/--
theorem `lieBracketWithin_congr_set'` / 定理 `lieBracketWithin_congr_set'`

English:
theorem lieBracketWithin_congr_set'
  given: (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]

中文:
定理 lieBracketWithin_congr_set'
  条件: (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]

Depends on / 依赖: fderivWithin_congr_set, lieBracketWithin
-/
theorem lieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]

/--
theorem `lieBracketWithin_congr_set` / 定理 `lieBracketWithin_congr_set`

English:
theorem lieBracketWithin_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: lieBracketWithin_congr_set' x h.filter_mono inf_le_left

中文:
定理 lieBracketWithin_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: lieBracketWithin_congr_set' x h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left, lieBracketWithin_congr_set
-/
theorem lieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
lieBracketWithin_congr_set' x h.filter_mono inf_le_left

/--
theorem `lieBracketWithin_eventually_congr_set'` / 定理 `lieBracketWithin_eventually_congr_set'`

English:
theorem lieBracketWithin_eventually_congr_set'
  given: (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y

中文:
定理 lieBracketWithin_eventually_congr_set'
  条件: (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y

Depends on / 依赖: eventually_nhds_nhdsWithin, lieBracketWithin_congr_set
-/
theorem lieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y

/--
theorem `lieBracketWithin_eventually_congr_set` / 定理 `lieBracketWithin_eventually_congr_set`

English:
theorem lieBracketWithin_eventually_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: lieBracketWithin_eventually_congr_set' x h.filter_mono inf_le_left

中文:
定理 lieBracketWithin_eventually_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: lieBracketWithin_eventually_congr_set' x h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left, lieBracketWithin_eventually_congr_set
-/
theorem lieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
lieBracketWithin_eventually_congr_set' x h.filter_mono inf_le_left

/--
theorem `_root_.DifferentiableWithinAt.lieBracketWithin_congr_mono` / 定理 `_root_.DifferentiableWithinAt.lieBracketWithin_congr_mono`

English:
theorem _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
  proof: by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

中文:
定理 _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
  证明: by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

Depends on / 依赖: fderivWithin_congr_mono, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, lieBracketWithin
-/
theorem _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
    (hV : DifferentiableWithinAt 𝕜 V s x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t subseteq s) :
    lieBracketWithin 𝕜 V₁ W₁ t x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

/--
theorem `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq` / 定理 `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq`

English:
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq
  proof: by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

中文:
定理 _root_.滤子.EventuallyEq.lieBracketWithin_vectorField_eq
  证明: by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

Depends on / 依赖: fderivWithin_eq, hV.fderivWithin_eq, hW.fderivWithin_eq, lieBracketWithin
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

/--
theorem `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem` / 定理 `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem`

English:
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
  proof: hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

中文:
定理 _root_.滤子.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
  证明: hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

Depends on / 依赖: hV.lieBracketWithin_vectorField_eq, lieBracketWithin_vectorField_eq, mem_of_mem_nhdsWithin
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x in s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/--
theorem `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField'` / 定理 `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField'`

English:
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField'
  proof: by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

中文:
定理 _root_.滤子.EventuallyEq.lieBracketWithin_vectorField'
  证明: by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

Depends on / 依赖: fderivWithin, filter_upwards, hV.fderivWithin, hW.fderivWithin, lieBracketWithin
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t subseteq s) :
    lieBracketWithin 𝕜 V₁ W₁ t =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

/--
theorem `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField` / 定理 `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField`

English:
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField
  proof: hV.lieBracketWithin_vectorField' hW Subset.rfl

中文:
定理 _root_.滤子.EventuallyEq.lieBracketWithin_vectorField
  证明: hV.lieBracketWithin_vectorField' hW Subset.rfl
-/
protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W s :=
  hV.lieBracketWithin_vectorField' hW Subset.rfl

/--
theorem `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert` / 定理 `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert`

English:
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
  proof: by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))

中文:
定理 _root_.滤子.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
  证明: by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))
-/
protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))

/--
theorem `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds` / 定理 `_root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds`

English:
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
  proof: (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

中文:
定理 _root_.滤子.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
  证明: (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

Depends on / 依赖: filter_mono, hV.filter_mono, hV.self_of_nhds, hW.filter_mono, hW.self_of_nhds, lieBracketWithin_vectorField_eq, nhdsWithin_le_nhds, self_of_nhds
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

/--
theorem `lieBracketWithin_congr` / 定理 `lieBracketWithin_congr`

English:
theorem lieBracketWithin_congr
  proof: (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

中文:
定理 lieBracketWithin_congr
  证明: (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

Depends on / 依赖: eventuallyEq, filter_mono, hV.eventuallyEq.filter_mono, hW.eventuallyEq.filter_mono, inf_le_right, lieBracketWithin_vectorField_eq
-/
theorem lieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/--
theorem `lieBracketWithin_congr'` / 定理 `lieBracketWithin_congr'`

English:
theorem lieBracketWithin_congr'
  given: (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x in s)
  proof: lieBracketWithin_congr hV (hV hx) hW (hW hx)

中文:
定理 lieBracketWithin_congr'
  条件: (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x in s)
  证明: lieBracketWithin_congr hV (hV hx) hW (hW hx)

Depends on / 依赖: lieBracketWithin_congr
-/
theorem lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x in s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  lieBracketWithin_congr hV (hV hx) hW (hW hx)

/--
theorem `_root_.Filter.EventuallyEq.lieBracket_vectorField_eq` / 定理 `_root_.Filter.EventuallyEq.lieBracket_vectorField_eq`

English:
theorem _root_.Filter.EventuallyEq.lieBracket_vectorField_eq
  proof: by
  rw [← lieBracketWithin_univ]; rw [← lieBracketWithin_univ]; rw [hV.lieBracketWithin_vectorField_eq_nhds hW]

中文:
定理 _root_.滤子.EventuallyEq.lieBracket_vectorField_eq
  证明: by
  rw [← lieBracketWithin_univ]; rw [← lieBracketWithin_univ]; rw [hV.lieBracketWithin_vectorField_eq_nhds hW]

Depends on / 依赖: hV.lieBracketWithin_vectorField_eq_nhds, lieBracketWithin_univ, lieBracketWithin_vectorField_eq_nhds
-/
theorem _root_.Filter.EventuallyEq.lieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracket 𝕜 V₁ W₁ x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ]; rw [← lieBracketWithin_univ]; rw [hV.lieBracketWithin_vectorField_eq_nhds hW]

/--
theorem `_root_.Filter.EventuallyEq.lieBracket_vectorField` / 定理 `_root_.Filter.EventuallyEq.lieBracket_vectorField`

English:
theorem _root_.Filter.EventuallyEq.lieBracket_vectorField
  proof: by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy

中文:
定理 _root_.滤子.EventuallyEq.lieBracket_vectorField
  证明: by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy
-/
protected theorem _root_.Filter.EventuallyEq.lieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : lieBracket 𝕜 V₁ W₁ =ᶠ[𝓝 x] lieBracket 𝕜 V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy

/--
lemma `leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt` / 引理 `leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt`

English:
lemma leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
  proof: by
  simp only [lieBracketWithin_eq, map_sub]
  have aux₁ {U V : E -> E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      DifferentiableWithinAt 𝕜 (fun x => (fderivWithin 𝕜 V s x) (U x)) s x :=
    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
    

中文:
引理 leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
  证明: by
  simp only [lieBracketWithin_eq, map_sub]
  have aux₁ {U V : E -> E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      DifferentiableWithinAt 𝕜 (fun x => (fderivWithin 𝕜 V s x) (U x)) s x :=
    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
    

Depends on / 依赖: ContDiffWithinAt, DifferentiableWithinAt, differentiableWithinAt, fderivWithin, fderivWithin_right_apply, hU.of_le, hV.fderivWithin_right_apply, le_rfl, lieBracketWithin_eq, map_sub, of_le, one_le_two, one_ne_zero, this.differentiableWithinAt
-/
lemma leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {U V W : E -> E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
    (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x)
    (hW : ContDiffWithinAt 𝕜 2 W s x)
    (h'U : IsSymmSndFDerivWithinAt 𝕜 U s x) (h'V : IsSymmSndFDerivWithinAt 𝕜 V s x)
    (h'W : IsSymmSndFDerivWithinAt 𝕜 W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  simp only [lieBracketWithin_eq, map_sub]
  have aux₁ {U V : E -> E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      DifferentiableWithinAt 𝕜 (fun x => (fderivWithin 𝕜 V s x) (U x)) s x :=
    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
    this.differentiableWithinAt one_ne_zero
  have aux₂ {U V : E -> E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      fderivWithin 𝕜 (fun y => (fderivWithin 𝕜 U s y) (V y)) s x =
        (fderivWithin 𝕜 U s x).comp (fderivWithin 𝕜 V s x) +
        (fderivWithin 𝕜 (fderivWithin 𝕜 U s) s x).flip (V x) := by
    refine fderivWithin_clm_apply (hs x hx) ?_ (hV.differentiableWithinAt two_ne_zero)
    exact (hU.fderivWithin_right hs le_rfl hx).differentiableWithinAt one_ne_zero
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hV hW) (aux₁ hW hV)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hV) (aux₁ hV hU)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hW) (aux₁ hW hU)]
  rw [aux₂ hW hV]; rw [aux₂ hV hW]; rw [aux₂ hV hU]; rw [aux₂ hU hV]; rw [aux₂ hW hU]; rw [aux₂ hU hW]
  simp only [FunLike.coe_sub, Pi.sub_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, h'V.eq, h'U.eq, h'W.eq]
  abel

/--
lemma `leibniz_identity_lieBracketWithin` / 引理 `leibniz_identity_lieBracketWithin`

English:
lemma leibniz_identity_lieBracketWithin
  statement: (hn : minSmoothness 𝕜 2 <= n)
  proof: by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx
    (hU.of_le (le_minSmoothness.trans hn)) (hV.of_le (le_minSmoothness.trans hn))
    (hW.of_le (le_minSmoothness.trans hn))
  · exact hU.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt hn hs h'x 

中文:
引理 leibniz_identity_lieBracketWithin
  结论: (hn : minSmoothness 𝕜 2 <= n)
  证明: by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx
    (hU.of_le (le_minSmoothness.trans hn)) (hV.of_le (le_minSmoothness.trans hn))
    (hW.of_le (le_minSmoothness.trans hn))
  · exact hU.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt hn hs h'x 

Depends on / 依赖: hU.isSymmSndFDerivWithinAt, hU.of_le, hV.isSymmSndFDerivWithinAt, hV.of_le, hW.isSymmSndFDerivWithinAt, hW.of_le, isSymmSndFDerivWithinAt, le_minSmoothness, le_minSmoothness.trans, leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt, of_le
-/
lemma leibniz_identity_lieBracketWithin (hn : minSmoothness 𝕜 2 <= n)
    {U V W : E -> E} {s : Set E} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (h'x : x in closure (interior s)) (hx : x in s)
    (hU : ContDiffWithinAt 𝕜 n U s x) (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx
    (hU.of_le (le_minSmoothness.trans hn)) (hV.of_le (le_minSmoothness.trans hn))
    (hW.of_le (le_minSmoothness.trans hn))
  · exact hU.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hW.isSymmSndFDerivWithinAt hn hs h'x hx

/--
lemma `leibniz_identity_lieBracket` / 引理 `leibniz_identity_lieBracket`

English:
lemma leibniz_identity_lieBracket
  statement: (hn : minSmoothness 𝕜 2 <= n) {U V W : E -> E} {x : E}
  proof: by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin hn uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW

中文:
引理 leibniz_identity_lieBracket
  结论: (hn : minSmoothness 𝕜 2 <= n) {U V W : E -> E} {x : E}
  证明: by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin hn uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW

Depends on / 依赖: contDiffWithinAt_univ, leibniz_identity_lieBracketWithin, lieBracketWithin_univ, mem_univ, uniqueDiffOn_univ
-/
lemma leibniz_identity_lieBracket (hn : minSmoothness 𝕜 2 <= n) {U V W : E -> E} {x : E}
    (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hW : ContDiffAt 𝕜 n W x) :
    lieBracket 𝕜 U (lieBracket 𝕜 V W) x =
      lieBracket 𝕜 (lieBracket 𝕜 U V) W x + lieBracket 𝕜 V (lieBracket 𝕜 U W) x := by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin hn uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW


/-!
### The pullback of vector fields in a vector space
-/

variable (𝕜) in
/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (f : E -> F) (V : F -> F) (x : E)
  body: (fderiv 𝕜 f x).inverse (V (f x))

中文:
定义 pullback
  签名: (f : E -> F) (V : F -> F) (x : E)
  定义体: (fderiv 𝕜 f x).inverse (V (f x))

Depends on / 依赖: fderiv, inverse
-/
def pullback (f : E -> F) (V : F -> F) (x : E) : E := (fderiv 𝕜 f x).inverse (V (f x))

variable (𝕜) in
/--
Definition of `pullbackWithin` / `pullbackWithin` 的定义

English:
definition pullbackWithin
  signature: (f : E -> F) (V : F -> F) (s : Set E) (x : E)
  body: (fderivWithin 𝕜 f s x).inverse (V (f x))

中文:
定义 pullbackWithin
  签名: (f : E -> F) (V : F -> F) (s : 集合 E) (x : E)
  定义体: (fderivWithin 𝕜 f s x).inverse (V (f x))

Depends on / 依赖: fderivWithin, inverse
-/
def pullbackWithin (f : E -> F) (V : F -> F) (s : Set E) (x : E) : E :=
  (fderivWithin 𝕜 f s x).inverse (V (f x))

/--
lemma `pullbackWithin_eq` / 引理 `pullbackWithin_eq`

English:
lemma pullbackWithin_eq
  given: {f : E -> F} {V : F -> F} {s : Set E}
  proof: rfl

中文:
引理 pullbackWithin_eq
  条件: {f : E -> F} {V : F -> F} {s : 集合 E}
  证明: rfl
-/
lemma pullbackWithin_eq {f : E -> F} {V : F -> F} {s : Set E} :
    pullbackWithin 𝕜 f V s = fun x => (fderivWithin 𝕜 f s x).inverse (V (f x)) := rfl

/--
lemma `pullback_eq_of_fderiv_eq` / 引理 `pullback_eq_of_fderiv_eq`

English:
lemma pullback_eq_of_fderiv_eq
  proof: by
  simp [pullback, ← hf]

中文:
引理 pullback_eq_of_fderiv_eq
  证明: by
  simp [pullback, ← hf]

Depends on / 依赖: pullback
-/
lemma pullback_eq_of_fderiv_eq
    {f : E -> F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F -> F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by
  simp [pullback, ← hf]

/--
lemma `pullback_eq_of_not_isInvertible` / 引理 `pullback_eq_of_not_isInvertible`

English:
lemma pullback_eq_of_not_isInvertible
  statement: {f : E -> F} {x : E}
  proof: by
  simp [pullback, h]

中文:
引理 pullback_eq_of_not_isInvertible
  结论: {f : E -> F} {x : E}
  证明: by
  simp [pullback, h]

Depends on / 依赖: pullback
-/
lemma pullback_eq_of_not_isInvertible {f : E -> F} {x : E}
    (h : ¬(fderiv 𝕜 f x).IsInvertible) (V : F -> F) :
    pullback 𝕜 f V x = 0 := by
  simp [pullback, h]

/--
lemma `pullbackWithin_eq_of_not_isInvertible` / 引理 `pullbackWithin_eq_of_not_isInvertible`

English:
lemma pullbackWithin_eq_of_not_isInvertible
  statement: {f : E -> F} {x : E}
  proof: by
  simp [pullbackWithin, h]

中文:
引理 pullbackWithin_eq_of_not_isInvertible
  结论: {f : E -> F} {x : E}
  证明: by
  simp [pullbackWithin, h]

Depends on / 依赖: pullbackWithin
-/
lemma pullbackWithin_eq_of_not_isInvertible {f : E -> F} {x : E}
    (h : ¬(fderivWithin 𝕜 f s x).IsInvertible) (V : F -> F) :
    pullbackWithin 𝕜 f V s x = 0 := by
  simp [pullbackWithin, h]

/--
lemma `pullbackWithin_eq_of_fderivWithin_eq` / 引理 `pullbackWithin_eq_of_fderivWithin_eq`

English:
lemma pullbackWithin_eq_of_fderivWithin_eq
  proof: by
  simp [pullbackWithin, ← hf]

中文:
引理 pullbackWithin_eq_of_fderivWithin_eq
  证明: by
  simp [pullbackWithin, ← hf]

Depends on / 依赖: pullbackWithin
-/
lemma pullbackWithin_eq_of_fderivWithin_eq
    {f : E -> F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderivWithin 𝕜 f s x) (V : F -> F) :
    pullbackWithin 𝕜 f V s x = M.symm (V (f x)) := by
  simp [pullbackWithin, ← hf]

/--
lemma `pullbackWithin_univ` / 引理 `pullbackWithin_univ`

English:
lemma pullbackWithin_univ
  given: {f : E -> F} {V : F -> F}
  proof: by
  ext x
  simp [pullbackWithin, pullback]

中文:
引理 pullbackWithin_univ
  条件: {f : E -> F} {V : F -> F}
  证明: by
  ext x
  simp [pullbackWithin, pullback]
-/
@[simp] lemma pullbackWithin_univ {f : E -> F} {V : F -> F} :
    pullbackWithin 𝕜 f V univ = pullback 𝕜 f V := by
  ext x
  simp [pullbackWithin, pullback]

open scoped Topology Filter

/--
lemma `fderiv_pullback` / 引理 `fderiv_pullback`

English:
lemma fderiv_pullback
  given: (f : E -> F) (V : F -> F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible)
  proof: by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

中文:
引理 fderiv_pullback
  条件: (f : E -> F) (V : F -> F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible)
  证明: by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

Depends on / 依赖: pullback_eq_of_fderiv_eq
-/
lemma fderiv_pullback (f : E -> F) (V : F -> F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible) :
    fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

/--
lemma `fderivWithin_pullbackWithin` / 引理 `fderivWithin_pullbackWithin`

English:
lemma fderivWithin_pullbackWithin
  statement: {f : E -> F} {V : F -> F} {x : E}
  proof: by
  rcases h'f with ⟨M, hM⟩
  simp [pullbackWithin_eq_of_fderivWithin_eq hM, ← hM]

中文:
引理 fderivWithin_pullbackWithin
  结论: {f : E -> F} {V : F -> F} {x : E}
  证明: by
  rcases h'f with ⟨M, hM⟩
  simp [pullbackWithin_eq_of_fderivWithin_eq hM, ← hM]

Depends on / 依赖: pullbackWithin_eq_of_fderivWithin_eq
-/
lemma fderivWithin_pullbackWithin {f : E -> F} {V : F -> F} {x : E}
    (h'f : (fderivWithin 𝕜 f s x).IsInvertible) :
    fderivWithin 𝕜 f s x (pullbackWithin 𝕜 f V s x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullbackWithin_eq_of_fderivWithin_eq hM, ← hM]

open Set

variable [CompleteSpace E]

/--
lemma `_root_.exists_continuousLinearEquiv_fderivWithin_symm_eq` / 引理 `_root_.exists_continuousLinearEquiv_fderivWithin_symm_eq`

English:
lemma _root_.exists_continuousLinearEquiv_fderivWithin_symm_eq
  proof: by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | exists (N : E ≃L[𝕜] F), N = fderivWithin 𝕜 f s y}
  have hU : U in 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F) in 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithi

中文:
引理 _root_.存在_continuousLinearEquiv_fderivWithin_symm_eq
  证明: by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | exists (N : E ≃L[𝕜] F), N = fderivWithin 𝕜 f s y}
  have hU : U in 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F) in 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithi

Depends on / 依赖: ContinuousWithinAt, M.nhds, classical, continuousWithinAt, f.fderivWithin_right, fderivWithin, fderivWithin_right, h.choose, le_rfl
-/
lemma _root_.exists_continuousLinearEquiv_fderivWithin_symm_eq
    {f : E -> F} {s : Set E} {x : E} (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    exists N : E -> (E ≃L[𝕜] F), ContDiffWithinAt 𝕜 1 (fun y => (N y : E ->L[𝕜] F)) s x
    ∧ ContDiffWithinAt 𝕜 1 (fun y => ((N y).symm : F ->L[𝕜] E)) s x
    ∧ (forallᶠ y in 𝓝[s] x, N y = fderivWithin 𝕜 f s y)
    ∧ forall v, fderivWithin 𝕜 (fun y => ((N y).symm : F ->L[𝕜] E)) s x v
      = - (N x).symm ∘L ((fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | exists (N : E ≃L[𝕜] F), N = fderivWithin 𝕜 f s y}
  have hU : U in 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F) in 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
      (h'f.fderivWithin_right (m := 1) hs le_rfl hx).continuousWithinAt
    exact this I
  let N : E -> (E ≃L[𝕜] F) := fun x => if h : x in U then h.choose else M
  have eN : (fun y => (N y : E ->L[𝕜] F)) =ᶠ[𝓝[s] x] fun y => fderivWithin 𝕜 f s y := by
    filter_upwards [hU] with y hy
    simpa only [hy, ↓reduceDIte, N] using Exists.choose_spec hy
  have e'N : N x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx eN
  have hN : ContDiffWithinAt 𝕜 1 (fun y => (N y : E ->L[𝕜] F)) s x := by
    have : ContDiffWithinAt 𝕜 1 (fun y => fderivWithin 𝕜 f s y) s x :=
      h'f.fderivWithin_right (m := 1) hs le_rfl hx
    apply this.congr_of_eventuallyEq eN e'N
  have hN' : ContDiffWithinAt 𝕜 1 (fun y => ((N y).symm : F ->L[𝕜] E)) s x := by
    have : ContDiffWithinAt 𝕜 1 (ContinuousLinearMap.inverse ∘ (fun y => (N y : E ->L[𝕜] F))) s x :=
      (contDiffAt_map_inverse (N x)).comp_contDiffWithinAt x hN
    convert! this with y
    simp only [Function.comp_apply, ContinuousLinearMap.inverse_equiv]
  refine ⟨N, hN, hN', eN, fun v => ?_⟩
  have A' y : ContinuousLinearMap.compL 𝕜 F E F (N y : E ->L[𝕜] F) ((N y).symm : F ->L[𝕜] E)
      = ContinuousLinearMap.id 𝕜 F := by ext; simp
  have : fderivWithin 𝕜 (fun y => ContinuousLinearMap.compL 𝕜 F E F (N y : E ->L[𝕜] F)
      ((N y).symm : F ->L[𝕜] E)) s x v = 0 := by
    simp [A', fderivWithin_const_apply]
  have I : (N x : E ->L[𝕜] F) ∘L (fderivWithin 𝕜 (fun y => ((N y).symm : F ->L[𝕜] E)) s x v) =
      - (fderivWithin 𝕜 (fun y => (N y : E ->L[𝕜] F)) s x v) ∘L ((N x).symm : F ->L[𝕜] E) := by
    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt one_ne_zero)
      (hN'.differentiableWithinAt one_ne_zero) (hs x hx)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F ->L[𝕜] E) : M = ((N x).symm : F ->L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderivWithin 𝕜 (fun y => ((N y).symm : F ->L[𝕜] E)) s x v), I]
  simp only [ContinuousLinearMap.comp_neg, eN.fderivWithin_eq e'N]

/--
lemma `DifferentiableWithinAt.pullbackWithin` / 引理 `DifferentiableWithinAt.pullbackWithin`

English:
lemma DifferentiableWithinAt.pullbackWithin
  statement: {f : E -> F} {V : F -> F} {s : Set E} {t : Set F} {x : E}
  proof: by
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
    with ⟨M, -, M_symm_smooth, hM, -⟩
  simp only [pullbackWithin_eq]
  have : DifferentiableWithinAt 𝕜 (fun y => ((M y).symm : F ->L[𝕜] E) (V (f y))) s x := by
    apply DifferentiableWithinAt.clm_apply
    · exact M_symm_sm

中文:
引理 DifferentiableWithinAt.pullbackWithin
  结论: {f : E -> F} {V : F -> F} {s : 集合 E} {t : 集合 F} {x : E}
  证明: by
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
    with ⟨M, -, M_symm_smooth, hM, -⟩
  simp only [pullbackWithin_eq]
  have : DifferentiableWithinAt 𝕜 (fun y => ((M y).symm : F ->L[𝕜] E) (V (f y))) s x := by
    apply DifferentiableWithinAt.clm_apply
    · exact M_symm_sm

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.clm_apply, M_symm_smooth, M_symm_smooth.differentiableWithinAt, clm_apply, congr_of_eventuallyEq, differentiableWithinAt, exists_continuousLinearEquiv_fderivWithin_symm_eq, fderivWithi, filter_upwards, hV.comp, hf.differentiableWithinAt, one_ne_zero, pullbackWithin_eq, this.congr_of_eventuallyEq, two_ne_zero
-/
lemma DifferentiableWithinAt.pullbackWithin {f : E -> F} {V : F -> F} {s : Set E} {t : Set F} {x : E}
    (hV : DifferentiableWithinAt 𝕜 V t (f x))
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hf' : (fderivWithin 𝕜 f s x).IsInvertible)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    DifferentiableWithinAt 𝕜 (pullbackWithin 𝕜 f V s) s x := by
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
    with ⟨M, -, M_symm_smooth, hM, -⟩
  simp only [pullbackWithin_eq]
  have : DifferentiableWithinAt 𝕜 (fun y => ((M y).symm : F ->L[𝕜] E) (V (f y))) s x := by
    apply DifferentiableWithinAt.clm_apply
    · exact M_symm_smooth.differentiableWithinAt one_ne_zero
    · exact hV.comp _ (hf.differentiableWithinAt two_ne_zero) hst
  apply this.congr_of_eventuallyEq
  · filter_upwards [hM] with y hy using by simp [← hy]
  · have hMx : M x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx hM
    simp [← hMx]

/--
lemma `_root_.exists_continuousLinearEquiv_fderiv_symm_eq` / 引理 `_root_.exists_continuousLinearEquiv_fderiv_symm_eq`

English:
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
  proof: by
  simp only [← fderivWithin_univ, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

中文:
引理 _root_.存在_continuousLinearEquiv_fderiv_symm_eq
  证明: by
  simp only [← fderivWithin_univ, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

Depends on / 依赖: contDiffWithinAt_univ, exists_continuousLinearEquiv_fderivWithin_symm_eq, fderivWithin_univ, mem_univ, nhdsWithin_univ, uniqueDiffOn_univ
-/
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
    {f : E -> F} {x : E} (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
    exists N : E -> (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y => (N y : E ->L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y => ((N y).symm : F ->L[𝕜] E)) x
    ∧ (forallᶠ y in 𝓝 x, N y = fderiv 𝕜 f y)
    ∧ forall v, fderiv 𝕜 (fun y => ((N y).symm : F ->L[𝕜] E)) x v
      = - (N x).symm ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x v)) ∘L (N x).symm := by
  simp only [← fderivWithin_univ, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

/--
lemma `pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt` / 引理 `pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt`

English:
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  proof: by
  by_cases h : (fderivWithin 𝕜 f s x).IsInvertible; swap
  · simp [pullbackWithin_eq_of_not_isInvertible h, lieBracketWithin_eq]
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq h'f h hu hx
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderivWithin 𝕜 f s x := (mem_of_mem

中文:
引理 pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  证明: by
  by_cases h : (fderivWithin 𝕜 f s x).IsInvertible; swap
  · simp [pullbackWithin_eq_of_not_isInvertible h, lieBracketWithin_eq]
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq h'f h hu hx
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderivWithin 𝕜 f s x := (mem_of_mem

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.fderivWithin_eq_of_mem, IsInvertible, M_diff, M_symm_smooth, exists_continuousLinearEquiv_fderivWithin_symm_eq, fderivWithin, fderivWithin_eq_of_mem, filter_up, lieBracketWithin_eq, mem_of_mem_nhdsWithin, pullbackWithin, pullbackWithin_eq_of_not_isInvertible
-/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : E -> F} {V W : F -> F} {x : E} {t : Set F}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x := by
  by_cases h : (fderivWithin 𝕜 f s x).IsInvertible; swap
  · simp [pullbackWithin_eq_of_not_isInvertible h, lieBracketWithin_eq]
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq h'f h hu hx
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderivWithin 𝕜 f s x := (mem_of_mem_nhdsWithin hx hM :)
  have AV : fderivWithin 𝕜 (pullbackWithin 𝕜 f V s) s x =
      fderivWithin 𝕜 (fun y => ((M y).symm : F ->L[𝕜] E) (V (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have AW : fderivWithin 𝕜 (pullbackWithin 𝕜 f W s) s x =
      fderivWithin 𝕜 (fun y => ((M y).symm : F ->L[𝕜] E) (W (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have Af : DifferentiableWithinAt 𝕜 f s x := h'f.differentiableWithinAt two_ne_zero
  simp only [lieBracketWithin_eq, pullbackWithin_eq_of_fderivWithin_eq hMx, map_sub, AV, AW]
  rw [fderivWithin_clm_apply]; rw [fderivWithin_clm_apply]
  · simp [fderivWithin_fun_comp x hW Af hst (hu x hx), ← hMx,
      fderivWithin_fun_comp x hV Af hst (hu x hx), M_diff, hf.eq]
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt one_ne_zero
  · exact hV.comp x Af hst
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt one_ne_zero
  · exact hW.comp x Af hst

/--
lemma `pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq` / 引理 `pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq`

English:
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
  proof: calc
  pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) u x := by
    simp only [pullbackWithin]
    congr 2
    exact fderivWithin_congr_set hus.symm
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V u) (pullbackWithin 𝕜 f W u) u x :=
    pullbackWi

中文:
引理 pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
  证明: calc
  pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) u x := by
    simp only [pullbackWithin]
    congr 2
    exact fderivWithin_congr_set hus.symm
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V u) (pullbackWithin 𝕜 f W u) u x :=
    pullbackWi
-/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
    {f : E -> F} {V W : F -> F} {x : E} {t : Set F} {u : Set E}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 u) (hx : x in u) (hst : MapsTo f u t) (hus : u =ᶠ[𝓝 x] s) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x := calc
  pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) u x := by
    simp only [pullbackWithin]
    congr 2
    exact fderivWithin_congr_set hus.symm
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V u) (pullbackWithin 𝕜 f W u) u x :=
    pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
      (hf.congr_set hus.symm) (h'f.congr_set hus.symm) hV hW hu hx hst
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) u x := by
    apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem _ _ hx
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x :=
    lieBracketWithin_congr_set hus

/--
lemma `pullback_lieBracket_of_isSymmSndFDerivAt` / 引理 `pullback_lieBracket_of_isSymmSndFDerivAt`

English:
lemma pullback_lieBracket_of_isSymmSndFDerivAt
  statement: {f : E -> F} {V W : F -> F} {x : E}
  proof: by
  simp only [← lieBracketWithin_univ, ← pullbackWithin_univ, ← isSymmSndFDerivWithinAt_univ,
    ← differentiableWithinAt_univ] at hf h'f hV hW ⊢
  exact pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt hf h'f hV hW uniqueDiffOn_univ
    (mem_univ _) (mapsTo_univ _ _)

中文:
引理 pullback_lieBracket_of_isSymmSndFDerivAt
  结论: {f : E -> F} {V W : F -> F} {x : E}
  证明: by
  simp only [← lieBracketWithin_univ, ← pullbackWithin_univ, ← isSymmSndFDerivWithinAt_univ,
    ← differentiableWithinAt_univ] at hf h'f hV hW ⊢
  exact pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt hf h'f hV hW uniqueDiffOn_univ
    (mem_univ _) (mapsTo_univ _ _)

Depends on / 依赖: differentiableWithinAt_univ, isSymmSndFDerivWithinAt_univ, lieBracketWithin_univ, mapsTo_univ, mem_univ, pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt, pullbackWithin_univ, uniqueDiffOn_univ
-/
lemma pullback_lieBracket_of_isSymmSndFDerivAt {f : E -> F} {V W : F -> F} {x : E}
    (hf : IsSymmSndFDerivAt 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x := by
  simp only [← lieBracketWithin_univ, ← pullbackWithin_univ, ← isSymmSndFDerivWithinAt_univ,
    ← differentiableWithinAt_univ] at hf h'f hV hW ⊢
  exact pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt hf h'f hV hW uniqueDiffOn_univ
    (mem_univ _) (mapsTo_univ _ _)

/--
lemma `pullbackWithin_lieBracketWithin` / 引理 `pullbackWithin_lieBracketWithin`

English:
lemma pullbackWithin_lieBracketWithin
  proof: pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  (h'f.isSymmSndFDerivWithinAt hn hu h'x hx) (h'f.of_le (le_minSmoothness.trans hn)) hV hW hu hx hst

中文:
引理 pullbackWithin_lieBracketWithin
  证明: pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  (h'f.isSymmSndFDerivWithinAt hn hu h'x hx) (h'f.of_le (le_minSmoothness.trans hn)) hV hW hu hx hst

Depends on / 依赖: f.isSymmSndFDerivWithinAt, f.of_le, isSymmSndFDerivWithinAt, le_minSmoothness, le_minSmoothness.trans, of_le, pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
-/
lemma pullbackWithin_lieBracketWithin
    {f : E -> F} {V W : F -> F} {x : E} {t : Set F} (hn : minSmoothness 𝕜 2 <= n)
    (h'f : ContDiffWithinAt 𝕜 n f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x in s) (h'x : x in closure (interior s)) (hst : MapsTo f s t) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x :=
  pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  (h'f.isSymmSndFDerivWithinAt hn hu h'x hx) (h'f.of_le (le_minSmoothness.trans hn)) hV hW hu hx hst

/--
lemma `pullback_lieBracket` / 引理 `pullback_lieBracket`

English:
lemma pullback_lieBracket
  statement: (hn : minSmoothness 𝕜 2 <= n)
  proof: pullback_lieBracket_of_isSymmSndFDerivAt (h'f.isSymmSndFDerivAt hn)
    (h'f.of_le (le_minSmoothness.trans hn)) hV hW

中文:
引理 pullback_lieBracket
  结论: (hn : minSmoothness 𝕜 2 <= n)
  证明: pullback_lieBracket_of_isSymmSndFDerivAt (h'f.isSymmSndFDerivAt hn)
    (h'f.of_le (le_minSmoothness.trans hn)) hV hW

Depends on / 依赖: f.isSymmSndFDerivAt, f.of_le, isSymmSndFDerivAt, le_minSmoothness, le_minSmoothness.trans, of_le, pullback_lieBracket_of_isSymmSndFDerivAt
-/
lemma pullback_lieBracket (hn : minSmoothness 𝕜 2 <= n)
    {f : E -> F} {V W : F -> F} {x : E} (h'f : ContDiffAt 𝕜 n f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x :=
  pullback_lieBracket_of_isSymmSndFDerivAt (h'f.isSymmSndFDerivAt hn)
    (h'f.of_le (le_minSmoothness.trans hn)) hV hW

end VectorField
