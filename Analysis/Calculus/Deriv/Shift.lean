/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Yaël Dillies
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
### Invariance of the derivative under translation

We show that if a function `f` has derivative `f'` at a point `a + x`, then `f (a + ·)`
has derivative `f'` at `x`. Similarly for `x + a`.
-/

public section

open scoped Pointwise

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 -> F} {f' : F}

/--
lemma `HasDerivAt.comp_const_add` / 引理 `HasDerivAt.comp_const_add`

English:
lemma HasDerivAt.comp_const_add
  given: (a x : 𝕜) (hf : HasDerivAt f f' (a + x))
  proof: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .const_add a hasDerivAt_id' x

中文:
引理 在点处可导.comp_const_add
  条件: (a x : 𝕜) (hf : 在点处可导 f f' (a + x))
  证明: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .const_add a hasDerivAt_id' x

Depends on / 依赖: Function, Function.comp_def, HasDerivAt, HasDerivAt.scomp, comp_def, const_add, hasDerivAt_id
-/
lemma HasDerivAt.comp_const_add (a x : 𝕜) (hf : HasDerivAt f f' (a + x)) :
    HasDerivAt (fun x => f (a + x)) f' x := by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .const_add a hasDerivAt_id' x

/--
lemma `HasDerivAt.comp_add_const` / 引理 `HasDerivAt.comp_add_const`

English:
lemma HasDerivAt.comp_add_const
  given: (x a : 𝕜) (hf : HasDerivAt f f' (x + a))
  proof: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .add_const a hasDerivAt_id' x

中文:
引理 在点处可导.comp_add_const
  条件: (x a : 𝕜) (hf : 在点处可导 f f' (x + a))
  证明: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .add_const a hasDerivAt_id' x

Depends on / 依赖: Function, Function.comp_def, HasDerivAt, HasDerivAt.scomp, add_const, comp_def, hasDerivAt_id
-/
lemma HasDerivAt.comp_add_const (x a : 𝕜) (hf : HasDerivAt f f' (x + a)) :
    HasDerivAt (fun x => f (x + a)) f' x := by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .add_const a hasDerivAt_id' x

/--
lemma `HasDerivAt.comp_const_sub` / 引理 `HasDerivAt.comp_const_sub`

English:
lemma HasDerivAt.comp_const_sub
  given: (a x : 𝕜) (hf : HasDerivAt f f' (a - x))
  proof: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .const_sub a hasDerivAt_id' x

中文:
引理 在点处可导.comp_const_sub
  条件: (a x : 𝕜) (hf : 在点处可导 f f' (a - x))
  证明: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .const_sub a hasDerivAt_id' x

Depends on / 依赖: Function, Function.comp_def, HasDerivAt, HasDerivAt.scomp, comp_def, const_sub, hasDerivAt_id
-/
lemma HasDerivAt.comp_const_sub (a x : 𝕜) (hf : HasDerivAt f f' (a - x)) :
    HasDerivAt (fun x => f (a - x)) (-f') x := by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .const_sub a hasDerivAt_id' x

/--
lemma `HasDerivAt.comp_sub_const` / 引理 `HasDerivAt.comp_sub_const`

English:
lemma HasDerivAt.comp_sub_const
  given: (x a : 𝕜) (hf : HasDerivAt f f' (x - a))
  proof: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .sub_const a hasDerivAt_id' x

中文:
引理 在点处可导.comp_sub_const
  条件: (x a : 𝕜) (hf : 在点处可导 f f' (x - a))
  证明: by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .sub_const a hasDerivAt_id' x

Depends on / 依赖: Function, Function.comp_def, HasDerivAt, HasDerivAt.scomp, comp_def, hasDerivAt_id, sub_const
-/
lemma HasDerivAt.comp_sub_const (x a : 𝕜) (hf : HasDerivAt f f' (x - a)) :
    HasDerivAt (fun x => f (x - a)) f' x := by
simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf .sub_const a hasDerivAt_id' x

variable (f)
variable (a : 𝕜) (s : Set 𝕜) (x : 𝕜)

/--
lemma `derivWithin_comp_neg` / 引理 `derivWithin_comp_neg`

English:
lemma derivWithin_comp_neg
  statement: derivWithin (f <| -·) s x = -derivWithin f (-s) (-x)
  proof: by
  simpa using derivWithin_comp_mul_left (-1) f s x

中文:
引理 derivWithin_comp_neg
  结论: derivWithin (f <| -·) s x = -derivWithin f (-s) (-x)
  证明: by
  simpa using derivWithin_comp_mul_left (-1) f s x

Depends on / 依赖: derivWithin_comp_mul_left
-/
lemma derivWithin_comp_neg : derivWithin (f <| -·) s x = -derivWithin f (-s) (-x) := by
  simpa using derivWithin_comp_mul_left (-1) f s x

/--
lemma `deriv_comp_neg` / 引理 `deriv_comp_neg`

English:
lemma deriv_comp_neg
  statement: deriv (fun x => f (-x)) x = -deriv f (-x)
  proof: by
  simpa using deriv_comp_mul_left (-1) f x

中文:
引理 deriv_comp_neg
  结论: deriv (fun x => f (-x)) x = -deriv f (-x)
  证明: by
  simpa using deriv_comp_mul_left (-1) f x

Depends on / 依赖: deriv_comp_mul_left
-/
lemma deriv_comp_neg : deriv (fun x => f (-x)) x = -deriv f (-x) := by
  simpa using deriv_comp_mul_left (-1) f x

/--
lemma `derivWithin_comp_const_add` / 引理 `derivWithin_comp_const_add`

English:
lemma derivWithin_comp_const_add
  proof: by
  simp only [derivWithin, fderivWithin_comp_add_left]

中文:
引理 derivWithin_comp_const_add
  证明: by
  simp only [derivWithin, fderivWithin_comp_add_left]

Depends on / 依赖: derivWithin, fderivWithin_comp_add_left
-/
lemma derivWithin_comp_const_add :
    derivWithin (f <| a + ·) s x = derivWithin f (a +ᵥ s) (a + x) := by
  simp only [derivWithin, fderivWithin_comp_add_left]

/--
lemma `deriv_comp_const_add` / 引理 `deriv_comp_const_add`

English:
lemma deriv_comp_const_add
  statement: deriv (fun x => f (a + x)) x = deriv f (a + x)
  proof: by
  simp only [deriv, fderiv_comp_add_left]

中文:
引理 deriv_comp_const_add
  结论: deriv (fun x => f (a + x)) x = deriv f (a + x)
  证明: by
  simp only [deriv, fderiv_comp_add_left]

Depends on / 依赖: fderiv_comp_add_left
-/
lemma deriv_comp_const_add : deriv (fun x => f (a + x)) x = deriv f (a + x) := by
  simp only [deriv, fderiv_comp_add_left]

/--
lemma `derivWithin_comp_add_const` / 引理 `derivWithin_comp_add_const`

English:
lemma derivWithin_comp_add_const
  proof: by
  simp only [derivWithin, fderivWithin_comp_add_right]

中文:
引理 derivWithin_comp_add_const
  证明: by
  simp only [derivWithin, fderivWithin_comp_add_right]

Depends on / 依赖: derivWithin, fderivWithin_comp_add_right
-/
lemma derivWithin_comp_add_const :
    derivWithin (f <| · + a) s x = derivWithin f (a +ᵥ s) (x + a) := by
  simp only [derivWithin, fderivWithin_comp_add_right]

/--
lemma `deriv_comp_add_const` / 引理 `deriv_comp_add_const`

English:
lemma deriv_comp_add_const
  statement: deriv (fun x => f (x + a)) x = deriv f (x + a)
  proof: by
  simpa [add_comm] using deriv_comp_const_add f a x

中文:
引理 deriv_comp_add_const
  结论: deriv (fun x => f (x + a)) x = deriv f (x + a)
  证明: by
  simpa [add_comm] using deriv_comp_const_add f a x

Depends on / 依赖: add_comm, deriv_comp_const_add
-/
lemma deriv_comp_add_const : deriv (fun x => f (x + a)) x = deriv f (x + a) := by
  simpa [add_comm] using deriv_comp_const_add f a x

/--
lemma `derivWithin_comp_const_sub` / 引理 `derivWithin_comp_const_sub`

English:
lemma derivWithin_comp_const_sub
  proof: by
  simp only [sub_eq_add_neg]
  rw [derivWithin_comp_neg (f <| a + ·)]; rw [derivWithin_comp_const_add]

中文:
引理 derivWithin_comp_const_sub
  证明: by
  simp only [sub_eq_add_neg]
  rw [derivWithin_comp_neg (f <| a + ·)]; rw [derivWithin_comp_const_add]

Depends on / 依赖: derivWithin_comp_const_add, derivWithin_comp_neg, sub_eq_add_neg
-/
lemma derivWithin_comp_const_sub :
    derivWithin (f <| a - ·) s x = -derivWithin f (a +ᵥ -s) (a - x) := by
  simp only [sub_eq_add_neg]
  rw [derivWithin_comp_neg (f <| a + ·)]; rw [derivWithin_comp_const_add]

/--
lemma `deriv_comp_const_sub` / 引理 `deriv_comp_const_sub`

English:
lemma deriv_comp_const_sub
  statement: deriv (fun x => f (a - x)) x = -deriv f (a - x)
  proof: by
  simp_rw [sub_eq_add_neg, deriv_comp_neg (f <| a + ·), deriv_comp_const_add]

中文:
引理 deriv_comp_const_sub
  结论: deriv (fun x => f (a - x)) x = -deriv f (a - x)
  证明: by
  simp_rw [sub_eq_add_neg, deriv_comp_neg (f <| a + ·), deriv_comp_const_add]

Depends on / 依赖: deriv_comp_const_add, deriv_comp_neg, simp_rw, sub_eq_add_neg
-/
lemma deriv_comp_const_sub : deriv (fun x => f (a - x)) x = -deriv f (a - x) := by
  simp_rw [sub_eq_add_neg, deriv_comp_neg (f <| a + ·), deriv_comp_const_add]

/--
lemma `derivWithin_comp_sub_const` / 引理 `derivWithin_comp_sub_const`

English:
lemma derivWithin_comp_sub_const
  proof: by
  simp_rw [sub_eq_add_neg, derivWithin_comp_add_const]

中文:
引理 derivWithin_comp_sub_const
  证明: by
  simp_rw [sub_eq_add_neg, derivWithin_comp_add_const]

Depends on / 依赖: derivWithin_comp_add_const, simp_rw, sub_eq_add_neg
-/
lemma derivWithin_comp_sub_const :
    derivWithin (fun x => f (x - a)) s x = derivWithin f (-a +ᵥ s) (x - a) := by
  simp_rw [sub_eq_add_neg, derivWithin_comp_add_const]

/--
lemma `deriv_comp_sub_const` / 引理 `deriv_comp_sub_const`

English:
lemma deriv_comp_sub_const
  statement: deriv (fun x => f (x - a)) x = deriv f (x - a)
  proof: by
  simp_rw [sub_eq_add_neg, deriv_comp_add_const]

中文:
引理 deriv_comp_sub_const
  结论: deriv (fun x => f (x - a)) x = deriv f (x - a)
  证明: by
  simp_rw [sub_eq_add_neg, deriv_comp_add_const]

Depends on / 依赖: deriv_comp_add_const, simp_rw, sub_eq_add_neg
-/
lemma deriv_comp_sub_const : deriv (fun x => f (x - a)) x = deriv f (x - a) := by
  simp_rw [sub_eq_add_neg, deriv_comp_add_const]
