/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# One-dimensional derivatives of sums etc

In this file we prove formulas about derivatives of `f + g`, `-f`, `f - g`, and `∑ i, f i x` for
functions from the base field to a normed space over this field.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section

universe u v w

open scoped Topology Filter ENNReal

open Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : 𝕜 -> F}
variable {f' g' : F}
variable {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
/--
theorem `HasDerivAtFilter.add` / 定理 `HasDerivAtFilter.add`

English:
theorem HasDerivAtFilter.add
  statement: (hf : HasDerivAtFilter f f' L)
  proof: by
  simpa using (hf.hasFDerivAtFilter.add hg.hasFDerivAtFilter).hasDerivAtFilter

@[to_fun]

中文:
定理 HasDerivAtFilter.add
  结论: (hf : HasDerivAtFilter f f' L)
  证明: by
  simpa using (hf.hasFDerivAtFilter.add hg.hasFDerivAtFilter).hasDerivAtFilter

@[to_fun]

Depends on / 依赖: hasDerivAtFilter, hasFDerivAtFilter, hf.hasFDerivAtFilter.add, hg.hasFDerivAtFilter
-/
theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L)
    (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L := by
  simpa using (hf.hasFDerivAtFilter.add hg.hasFDerivAtFilter).hasDerivAtFilter

@[to_fun]
/--
theorem `HasStrictDerivAt.add` / 定理 `HasStrictDerivAt.add`

English:
theorem HasStrictDerivAt.add
  given: (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
  proof: HasDerivAtFilter.add hf hg

@[to_fun]

中文:
定理 HasStrictDerivAt.add
  条件: (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
  证明: HasDerivAtFilter.add hf hg

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.add
-/
theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (f + g) (f' + g') x :=
  HasDerivAtFilter.add hf hg

@[to_fun]
/--
theorem `HasDerivWithinAt.add` / 定理 `HasDerivWithinAt.add`

English:
theorem HasDerivWithinAt.add
  statement: (hf : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.add hf hg

@[to_fun]

中文:
定理 HasDerivWithinAt.add
  结论: (hf : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.add hf hg

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.add
-/
theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f + g) (f' + g') s x :=
  HasDerivAtFilter.add hf hg

@[to_fun]
/--
theorem `HasDerivAt.add` / 定理 `HasDerivAt.add`

English:
theorem HasDerivAt.add
  given: (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
  proof: HasDerivAtFilter.add hf hg

中文:
定理 HasDerivAt.add
  条件: (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
  证明: HasDerivAtFilter.add hf hg

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.add
-/
theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f + g) (f' + g') x :=
  HasDerivAtFilter.add hf hg

/--
theorem `derivWithin_fun_add` / 定理 `derivWithin_fun_add`

English:
theorem derivWithin_fun_add
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_add
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hf.hasDerivWithinAt.add, hg.hasDerivWithinAt
-/
theorem derivWithin_fun_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y + g y) s x = derivWithin f s x + derivWithin g s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_add` / 定理 `derivWithin_add`

English:
theorem derivWithin_add
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: derivWithin_fun_add hf hg

@[simp]

中文:
定理 derivWithin_add
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: derivWithin_fun_add hf hg

@[simp]

Depends on / 依赖: derivWithin_fun_add
-/
theorem derivWithin_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (f + g) s x = derivWithin f s x + derivWithin g s x :=
  derivWithin_fun_add hf hg

@[simp]
/--
theorem `deriv_fun_add` / 定理 `deriv_fun_add`

English:
theorem deriv_fun_add
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]

中文:
定理 deriv_fun_add
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.add, hg.hasDerivAt
-/
theorem deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
/--
theorem `deriv_add` / 定理 `deriv_add`

English:
theorem deriv_add
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]

中文:
定理 deriv_add
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.add, hg.hasDerivAt
-/
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
/--
theorem `hasDerivAtFilter_add_const_iff` / 定理 `hasDerivAtFilter_add_const_iff`

English:
theorem hasDerivAtFilter_add_const_iff
  given: (c : F)
  proof: hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAtFilter.add_const⟩ := hasDerivAtFilter_add_const_iff

@[simp]

中文:
定理 hasDerivAtFilter_add_const_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAtFilter.add_const⟩ := hasDerivAtFilter_add_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_add_const_iff
-/
theorem hasDerivAtFilter_add_const_iff (c : F) :
    HasDerivAtFilter (f · + c) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAtFilter.add_const⟩ := hasDerivAtFilter_add_const_iff

@[simp]
/--
theorem `hasStrictDerivAt_add_const_iff` / 定理 `hasStrictDerivAt_add_const_iff`

English:
theorem hasStrictDerivAt_add_const_iff
  given: (c : F)
  proof: hasDerivAtFilter_add_const_iff c

alias ⟨_, HasStrictDerivAt.add_const⟩ := hasStrictDerivAt_add_const_iff

@[simp]

中文:
定理 hasStrictDerivAt_add_const_iff
  条件: (c : F)
  证明: hasDerivAtFilter_add_const_iff c

alias ⟨_, HasStrictDerivAt.add_const⟩ := hasStrictDerivAt_add_const_iff

@[simp]

Depends on / 依赖: hasDerivAtFilter_add_const_iff
-/
theorem hasStrictDerivAt_add_const_iff (c : F) :
    HasStrictDerivAt (f · + c) f' x ↔ HasStrictDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasStrictDerivAt.add_const⟩ := hasStrictDerivAt_add_const_iff

@[simp]
/--
theorem `hasDerivWithinAt_add_const_iff` / 定理 `hasDerivWithinAt_add_const_iff`

English:
theorem hasDerivWithinAt_add_const_iff
  given: (c : F)
  proof: hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivWithinAt.add_const⟩ := hasDerivWithinAt_add_const_iff

@[simp]

中文:
定理 hasDerivWithinAt_add_const_iff
  条件: (c : F)
  证明: hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivWithinAt.add_const⟩ := hasDerivWithinAt_add_const_iff

@[simp]

Depends on / 依赖: hasDerivAtFilter_add_const_iff
-/
theorem hasDerivWithinAt_add_const_iff (c : F) :
    HasDerivWithinAt (f · + c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivWithinAt.add_const⟩ := hasDerivWithinAt_add_const_iff

@[simp]
/--
theorem `hasDerivAt_add_const_iff` / 定理 `hasDerivAt_add_const_iff`

English:
theorem hasDerivAt_add_const_iff
  given: (c : F)
  statement: HasDerivAt (f · + c) f' x ↔ HasDerivAt f f' x
  proof: hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAt.add_const⟩ := hasDerivAt_add_const_iff

中文:
定理 hasDerivAt_add_const_iff
  条件: (c : F)
  结论: HasDerivAt (f · + c) f' x ↔ HasDerivAt f f' x
  证明: hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAt.add_const⟩ := hasDerivAt_add_const_iff

Depends on / 依赖: hasDerivAtFilter_add_const_iff
-/
theorem hasDerivAt_add_const_iff (c : F) : HasDerivAt (f · + c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAt.add_const⟩ := hasDerivAt_add_const_iff

/--
theorem `derivWithin_add_const` / 定理 `derivWithin_add_const`

English:
theorem derivWithin_add_const
  given: (c : F)
  proof: by
  simp only [derivWithin, fderivWithin_add_const]

中文:
定理 derivWithin_add_const
  条件: (c : F)
  证明: by
  simp only [derivWithin, fderivWithin_add_const]

Depends on / 依赖: derivWithin, fderivWithin_add_const
-/
theorem derivWithin_add_const (c : F) :
    derivWithin (fun y => f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_add_const]

/--
theorem `deriv_add_const` / 定理 `deriv_add_const`

English:
theorem deriv_add_const
  given: (c : F)
  statement: deriv (fun y => f y + c) x = deriv f x
  proof: by
  simp only [deriv, fderiv_add_const]

@[simp]

中文:
定理 deriv_add_const
  条件: (c : F)
  结论: deriv (fun y => f y + c) x = deriv f x
  证明: by
  simp only [deriv, fderiv_add_const]

@[simp]

Depends on / 依赖: fderiv_add_const
-/
theorem deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]

@[simp]
/--
theorem `deriv_add_const'` / 定理 `deriv_add_const'`

English:
theorem deriv_add_const'
  given: (c : F)
  statement: (deriv fun y => f y + c) = deriv f
  proof: funext fun _ => deriv_add_const c

中文:
定理 deriv_add_const'
  条件: (c : F)
  结论: (deriv fun y => f y + c) = deriv f
  证明: funext fun _ => deriv_add_const c

Depends on / 依赖: deriv_add_const
-/
theorem deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f :=
  funext fun _ => deriv_add_const c

/--
theorem `hasDerivAtFilter_const_add_iff` / 定理 `hasDerivAtFilter_const_add_iff`

English:
theorem hasDerivAtFilter_const_add_iff
  given: (c : F)
  proof: hasFDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAtFilter.const_add⟩ := hasDerivAtFilter_const_add_iff

@[simp]

中文:
定理 hasDerivAtFilter_const_add_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAtFilter.const_add⟩ := hasDerivAtFilter_const_add_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_const_add_iff
-/
theorem hasDerivAtFilter_const_add_iff (c : F) :
    HasDerivAtFilter (c + f ·) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAtFilter.const_add⟩ := hasDerivAtFilter_const_add_iff

@[simp]
/--
theorem `hasStrictDerivAt_const_add_iff` / 定理 `hasStrictDerivAt_const_add_iff`

English:
theorem hasStrictDerivAt_const_add_iff
  given: (c : F)
  proof: hasDerivAtFilter_const_add_iff c

alias ⟨_, HasStrictDerivAt.const_add⟩ := hasStrictDerivAt_const_add_iff

@[simp]

中文:
定理 hasStrictDerivAt_const_add_iff
  条件: (c : F)
  证明: hasDerivAtFilter_const_add_iff c

alias ⟨_, HasStrictDerivAt.const_add⟩ := hasStrictDerivAt_const_add_iff

@[simp]

Depends on / 依赖: hasDerivAtFilter_const_add_iff
-/
theorem hasStrictDerivAt_const_add_iff (c : F) :
    HasStrictDerivAt (c + f ·) f' x ↔ HasStrictDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasStrictDerivAt.const_add⟩ := hasStrictDerivAt_const_add_iff

@[simp]
/--
theorem `hasDerivWithinAt_const_add_iff` / 定理 `hasDerivWithinAt_const_add_iff`

English:
theorem hasDerivWithinAt_const_add_iff
  given: (c : F)
  proof: hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivWithinAt.const_add⟩ := hasDerivWithinAt_const_add_iff

@[simp]

中文:
定理 hasDerivWithinAt_const_add_iff
  条件: (c : F)
  证明: hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivWithinAt.const_add⟩ := hasDerivWithinAt_const_add_iff

@[simp]

Depends on / 依赖: hasDerivAtFilter_const_add_iff
-/
theorem hasDerivWithinAt_const_add_iff (c : F) :
    HasDerivWithinAt (c + f ·) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivWithinAt.const_add⟩ := hasDerivWithinAt_const_add_iff

@[simp]
/--
theorem `hasDerivAt_const_add_iff` / 定理 `hasDerivAt_const_add_iff`

English:
theorem hasDerivAt_const_add_iff
  given: (c : F)
  statement: HasDerivAt (c + f ·) f' x ↔ HasDerivAt f f' x
  proof: hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAt.const_add⟩ := hasDerivAt_const_add_iff

中文:
定理 hasDerivAt_const_add_iff
  条件: (c : F)
  结论: HasDerivAt (c + f ·) f' x ↔ HasDerivAt f f' x
  证明: hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAt.const_add⟩ := hasDerivAt_const_add_iff

Depends on / 依赖: hasDerivAtFilter_const_add_iff
-/
theorem hasDerivAt_const_add_iff (c : F) : HasDerivAt (c + f ·) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAt.const_add⟩ := hasDerivAt_const_add_iff

/--
theorem `derivWithin_const_add` / 定理 `derivWithin_const_add`

English:
theorem derivWithin_const_add
  given: (c : F)
  proof: by
  simp only [derivWithin, fderivWithin_const_add]

@[simp]

中文:
定理 derivWithin_const_add
  条件: (c : F)
  证明: by
  simp only [derivWithin, fderivWithin_const_add]

@[simp]

Depends on / 依赖: derivWithin, fderivWithin_const_add
-/
theorem derivWithin_const_add (c : F) :
    derivWithin (c + f ·) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_const_add]

@[simp]
/--
theorem `derivWithin_const_add_fun` / 定理 `derivWithin_const_add_fun`

English:
theorem derivWithin_const_add_fun
  given: (c : F)
  proof: by
  ext
  apply derivWithin_const_add

中文:
定理 derivWithin_const_add_fun
  条件: (c : F)
  证明: by
  ext
  apply derivWithin_const_add

Depends on / 依赖: derivWithin_const_add
-/
theorem derivWithin_const_add_fun (c : F) :
    derivWithin (c + f ·) = derivWithin f := by
  ext
  apply derivWithin_const_add

/--
theorem `deriv_const_add` / 定理 `deriv_const_add`

English:
theorem deriv_const_add
  given: (c : F)
  statement: deriv (c + f ·) x = deriv f x
  proof: by
  simp only [deriv, fderiv_const_add]

@[simp]

中文:
定理 deriv_const_add
  条件: (c : F)
  结论: deriv (c + f ·) x = deriv f x
  证明: by
  simp only [deriv, fderiv_const_add]

@[simp]

Depends on / 依赖: fderiv_const_add
-/
theorem deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x := by
  simp only [deriv, fderiv_const_add]

@[simp]
/--
theorem `deriv_const_add'` / 定理 `deriv_const_add'`

English:
theorem deriv_const_add'
  given: (c : F)
  statement: (deriv (c + f ·)) = deriv f
  proof: funext fun _ => deriv_const_add c

中文:
定理 deriv_const_add'
  条件: (c : F)
  结论: (deriv (c + f ·)) = deriv f
  证明: funext fun _ => deriv_const_add c

Depends on / 依赖: deriv_const_add
-/
theorem deriv_const_add' (c : F) : (deriv (c + f ·)) = deriv f :=
  funext fun _ => deriv_const_add c

/--
theorem `deriv_const_add_id` / 定理 `deriv_const_add_id`

English:
theorem deriv_const_add_id
  given: (c : 𝕜)
  statement: deriv (c + ·) x = 1
  proof: by
  rw [deriv_const_add c]; rw [deriv_id'']

@[simp]

中文:
定理 deriv_const_add_id
  条件: (c : 𝕜)
  结论: deriv (c + ·) x = 1
  证明: by
  rw [deriv_const_add c]; rw [deriv_id'']

@[simp]

Depends on / 依赖: deriv_const_add, deriv_id
-/
theorem deriv_const_add_id (c : 𝕜) : deriv (c + ·) x = 1 := by
  rw [deriv_const_add c]; rw [deriv_id'']

@[simp]
/--
theorem `deriv_const_add_id'` / 定理 `deriv_const_add_id'`

English:
theorem deriv_const_add_id'
  given: (c : 𝕜)
  statement: (deriv (c + ·)) = fun _ => 1
  proof: funext fun _ => deriv_const_add_id c

中文:
定理 deriv_const_add_id'
  条件: (c : 𝕜)
  结论: (deriv (c + ·)) = fun _ => 1
  证明: funext fun _ => deriv_const_add_id c

Depends on / 依赖: deriv_const_add_id
-/
theorem deriv_const_add_id' (c : 𝕜) : (deriv (c + ·)) = fun _ => 1 :=
  funext fun _ => deriv_const_add_id c

/--
lemma `differentiableAt_comp_add_const` / 引理 `differentiableAt_comp_add_const`

English:
lemma differentiableAt_comp_add_const
  given: {a b : 𝕜}
  proof: by
  grind [add_comm, differentiableAt_comp_add_left]

中文:
引理 differentiableAt_comp_add_const
  条件: {a b : 𝕜}
  证明: by
  grind [add_comm, differentiableAt_comp_add_left]

Depends on / 依赖: add_comm, differentiableAt_comp_add_left
-/
lemma differentiableAt_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x => f (x + b)) a ↔ DifferentiableAt 𝕜 f (a + b) := by
  grind [add_comm, differentiableAt_comp_add_left]

/--
lemma `differentiableAt_iff_comp_const_add` / 引理 `differentiableAt_iff_comp_const_add`

English:
lemma differentiableAt_iff_comp_const_add
  given: {a b : 𝕜}
  proof: by
  simp [differentiableAt_comp_add_left]

中文:
引理 differentiableAt_iff_comp_const_add
  条件: {a b : 𝕜}
  证明: by
  simp [differentiableAt_comp_add_left]

Depends on / 依赖: differentiableAt_comp_add_left
-/
lemma differentiableAt_iff_comp_const_add {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (b + x)) (-b + a) := by
  simp [differentiableAt_comp_add_left]

/--
lemma `differentiableAt_iff_comp_add_const` / 引理 `differentiableAt_iff_comp_add_const`

English:
lemma differentiableAt_iff_comp_add_const
  given: {a b : 𝕜}
  proof: by
  simp [differentiableAt_comp_add_const]

中文:
引理 differentiableAt_iff_comp_add_const
  条件: {a b : 𝕜}
  证明: by
  simp [differentiableAt_comp_add_const]

Depends on / 依赖: differentiableAt_comp_add_const
-/
lemma differentiableAt_iff_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (x + b)) (a - b) := by
  simp [differentiableAt_comp_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/

variable {ι : Type*} {u : Finset ι} {A : ι -> 𝕜 -> F} {A' : ι -> F}

/--
theorem `HasDerivAtFilter.fun_sum` / 定理 `HasDerivAtFilter.fun_sum`

English:
theorem HasDerivAtFilter.fun_sum
  given: (h : forall i in u, HasDerivAtFilter (A i) (A' i) L)
  proof: by
  simpa using (HasFDerivAtFilter.fun_sum h).hasDerivAtFilter

中文:
定理 HasDerivAtFilter.fun_sum
  条件: (h : 对任意 i in u, HasDerivAtFilter (A i) (A' i) L)
  证明: by
  simpa using (HasFDerivAtFilter.fun_sum h).hasDerivAtFilter

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.fun_sum, fun_sum, hasDerivAtFilter
-/
theorem HasDerivAtFilter.fun_sum (h : forall i in u, HasDerivAtFilter (A i) (A' i) L) :
    HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) L := by
  simpa using (HasFDerivAtFilter.fun_sum h).hasDerivAtFilter

/--
theorem `HasDerivAtFilter.sum` / 定理 `HasDerivAtFilter.sum`

English:
theorem HasDerivAtFilter.sum
  given: (h : forall i in u, HasDerivAtFilter (A i) (A' i) L)
  proof: by
  convert! HasDerivAtFilter.fun_sum h
  simp

中文:
定理 HasDerivAtFilter.sum
  条件: (h : 对任意 i in u, HasDerivAtFilter (A i) (A' i) L)
  证明: by
  convert! HasDerivAtFilter.fun_sum h
  simp

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.fun_sum, convert, fun_sum
-/
theorem HasDerivAtFilter.sum (h : forall i in u, HasDerivAtFilter (A i) (A' i) L) :
    HasDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L := by
  convert! HasDerivAtFilter.fun_sum h
  simp

/--
theorem `HasStrictDerivAt.fun_sum` / 定理 `HasStrictDerivAt.fun_sum`

English:
theorem HasStrictDerivAt.fun_sum
  given: (h : forall i in u, HasStrictDerivAt (A i) (A' i) x)
  proof: HasDerivAtFilter.fun_sum h

中文:
定理 HasStrictDerivAt.fun_sum
  条件: (h : 对任意 i in u, HasStrictDerivAt (A i) (A' i) x)
  证明: HasDerivAtFilter.fun_sum h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.fun_sum, fun_sum
-/
theorem HasStrictDerivAt.fun_sum (h : forall i in u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasDerivAtFilter.fun_sum h

/--
theorem `HasStrictDerivAt.sum` / 定理 `HasStrictDerivAt.sum`

English:
theorem HasStrictDerivAt.sum
  given: (h : forall i in u, HasStrictDerivAt (A i) (A' i) x)
  proof: HasDerivAtFilter.sum h

中文:
定理 HasStrictDerivAt.sum
  条件: (h : 对任意 i in u, HasStrictDerivAt (A i) (A' i) x)
  证明: HasDerivAtFilter.sum h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.sum
-/
theorem HasStrictDerivAt.sum (h : forall i in u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (∑ i in u, A i) (∑ i in u, A' i) x :=
  HasDerivAtFilter.sum h

/--
theorem `HasDerivWithinAt.fun_sum` / 定理 `HasDerivWithinAt.fun_sum`

English:
theorem HasDerivWithinAt.fun_sum
  given: (h : forall i in u, HasDerivWithinAt (A i) (A' i) s x)
  proof: HasDerivAtFilter.fun_sum h

中文:
定理 HasDerivWithinAt.fun_sum
  条件: (h : 对任意 i in u, HasDerivWithinAt (A i) (A' i) s x)
  证明: HasDerivAtFilter.fun_sum h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.fun_sum, fun_sum
-/
theorem HasDerivWithinAt.fun_sum (h : forall i in u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasDerivAtFilter.fun_sum h

/--
theorem `HasDerivWithinAt.sum` / 定理 `HasDerivWithinAt.sum`

English:
theorem HasDerivWithinAt.sum
  given: (h : forall i in u, HasDerivWithinAt (A i) (A' i) s x)
  proof: HasDerivAtFilter.sum h

中文:
定理 HasDerivWithinAt.sum
  条件: (h : 对任意 i in u, HasDerivWithinAt (A i) (A' i) s x)
  证明: HasDerivAtFilter.sum h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.sum
-/
theorem HasDerivWithinAt.sum (h : forall i in u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i) s x :=
  HasDerivAtFilter.sum h

/--
theorem `HasDerivAt.fun_sum` / 定理 `HasDerivAt.fun_sum`

English:
theorem HasDerivAt.fun_sum
  given: (h : forall i in u, HasDerivAt (A i) (A' i) x)
  proof: HasDerivAtFilter.fun_sum h

中文:
定理 HasDerivAt.fun_sum
  条件: (h : 对任意 i in u, HasDerivAt (A i) (A' i) x)
  证明: HasDerivAtFilter.fun_sum h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.fun_sum, fun_sum
-/
theorem HasDerivAt.fun_sum (h : forall i in u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasDerivAtFilter.fun_sum h

/--
theorem `HasDerivAt.sum` / 定理 `HasDerivAt.sum`

English:
theorem HasDerivAt.sum
  given: (h : forall i in u, HasDerivAt (A i) (A' i) x)
  proof: HasDerivAtFilter.sum h

中文:
定理 HasDerivAt.sum
  条件: (h : 对任意 i in u, HasDerivAt (A i) (A' i) x)
  证明: HasDerivAtFilter.sum h

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.sum
-/
theorem HasDerivAt.sum (h : forall i in u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (∑ i in u, A i) (∑ i in u, A' i) x :=
  HasDerivAtFilter.sum h

/--
theorem `derivWithin_fun_sum` / 定理 `derivWithin_fun_sum`

English:
theorem derivWithin_fun_sum
  given: (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_sum
  条件: (h : 对任意 i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.fun_sum, UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, fun_sum, hasDerivWithinAt
-/
theorem derivWithin_fun_sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y => ∑ i in u, A i y) s x = ∑ i in u, derivWithin (A i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_sum` / 定理 `derivWithin_sum`

English:
theorem derivWithin_sum
  given: (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp]

中文:
定理 derivWithin_sum
  条件: (h : 对任意 i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp]

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.sum, UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt
-/
theorem derivWithin_sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (∑ i in u, A i) s x = ∑ i in u, derivWithin (A i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp]
/--
theorem `deriv_fun_sum` / 定理 `deriv_fun_sum`

English:
theorem deriv_fun_sum
  given: (h : forall i in u, DifferentiableAt 𝕜 (A i) x)
  proof: (HasDerivAt.fun_sum fun i hi => (h i hi).hasDerivAt).deriv

@[simp]

中文:
定理 deriv_fun_sum
  条件: (h : 对任意 i in u, DifferentiableAt 𝕜 (A i) x)
  证明: (HasDerivAt.fun_sum fun i hi => (h i hi).hasDerivAt).deriv

@[simp]

Depends on / 依赖: HasDerivAt, HasDerivAt.fun_sum, fun_sum, hasDerivAt
-/
theorem deriv_fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
  (HasDerivAt.fun_sum fun i hi => (h i hi).hasDerivAt).deriv

@[simp]
/--
theorem `deriv_sum` / 定理 `deriv_sum`

English:
theorem deriv_sum
  given: (h : forall i in u, DifferentiableAt 𝕜 (A i) x)
  proof: (HasDerivAt.sum fun i hi => (h i hi).hasDerivAt).deriv

中文:
定理 deriv_sum
  条件: (h : 对任意 i in u, DifferentiableAt 𝕜 (A i) x)
  证明: (HasDerivAt.sum fun i hi => (h i hi).hasDerivAt).deriv

Depends on / 依赖: HasDerivAt, HasDerivAt.sum, hasDerivAt
-/
theorem deriv_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
    deriv (∑ i in u, A i) x = ∑ i in u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi => (h i hi).hasDerivAt).deriv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/

@[to_fun]
/--
theorem `HasDerivAtFilter.neg` / 定理 `HasDerivAtFilter.neg`

English:
theorem HasDerivAtFilter.neg
  given: (h : HasDerivAtFilter f f' L)
  proof: by simpa using (HasFDerivAtFilter.neg h).hasDerivAtFilter

@[to_fun]

中文:
定理 HasDerivAtFilter.neg
  条件: (h : HasDerivAtFilter f f' L)
  证明: by simpa using (HasFDerivAtFilter.neg h).hasDerivAtFilter

@[to_fun]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.neg, hasDerivAtFilter
-/
theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (-f) (-f') L := by simpa using (HasFDerivAtFilter.neg h).hasDerivAtFilter

@[to_fun]
/--
theorem `HasDerivWithinAt.neg` / 定理 `HasDerivWithinAt.neg`

English:
theorem HasDerivWithinAt.neg
  given: (h : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.neg h

@[to_fun]

中文:
定理 HasDerivWithinAt.neg
  条件: (h : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.neg h

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.neg
-/
theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (-f) (-f') s x :=
  HasDerivAtFilter.neg h

@[to_fun]
/--
theorem `HasDerivAt.neg` / 定理 `HasDerivAt.neg`

English:
theorem HasDerivAt.neg
  given: (h : HasDerivAt f f' x)
  statement: HasDerivAt (-f) (-f') x
  proof: HasDerivAtFilter.neg h

@[to_fun]

中文:
定理 HasDerivAt.neg
  条件: (h : HasDerivAt f f' x)
  结论: HasDerivAt (-f) (-f') x
  证明: HasDerivAtFilter.neg h

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.neg
-/
theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f) (-f') x :=
  HasDerivAtFilter.neg h

@[to_fun]
/--
theorem `HasStrictDerivAt.neg` / 定理 `HasStrictDerivAt.neg`

English:
theorem HasStrictDerivAt.neg
  given: (h : HasStrictDerivAt f f' x)
  statement: HasStrictDerivAt (-f) (-f') x
  proof: HasDerivAtFilter.neg h

@[to_fun]

中文:
定理 HasStrictDerivAt.neg
  条件: (h : HasStrictDerivAt f f' x)
  结论: HasStrictDerivAt (-f) (-f') x
  证明: HasDerivAtFilter.neg h

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.neg
-/
theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) : HasStrictDerivAt (-f) (-f') x :=
  HasDerivAtFilter.neg h

@[to_fun]
/--
theorem `derivWithin.neg` / 定理 `derivWithin.neg`

English:
theorem derivWithin.neg
  statement: derivWithin (-f) s x = -derivWithin f s x
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp only [derivWithin, fderivWithin_neg hsx, neg_apply]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun]

中文:
定理 derivWithin.neg
  结论: derivWithin (-f) s x = -derivWithin f s x
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp only [derivWithin, fderivWithin_neg hsx, neg_apply]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, fderivWithin_neg, neg_apply
-/
theorem derivWithin.neg : derivWithin (-f) s x = -derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp only [derivWithin, fderivWithin_neg hsx, neg_apply]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun]
/--
theorem `deriv.neg` / 定理 `deriv.neg`

English:
theorem deriv.neg
  statement: deriv (-f) x = -deriv f x
  proof: by
  simp only [deriv, fderiv_neg, neg_apply]

@[to_fun (attr := simp)]

中文:
定理 deriv.neg
  结论: deriv (-f) x = -deriv f x
  证明: by
  simp only [deriv, fderiv_neg, neg_apply]

@[to_fun (attr := simp)]

Depends on / 依赖: fderiv_neg, neg_apply
-/
theorem deriv.neg : deriv (-f) x = -deriv f x := by
  simp only [deriv, fderiv_neg, neg_apply]

@[to_fun (attr := simp)]
/--
theorem `deriv.neg'` / 定理 `deriv.neg'`

English:
theorem deriv.neg'
  statement: (deriv (-f)) = fun x => -deriv f x
  proof: funext fun _ => deriv.neg

中文:
定理 deriv.neg'
  结论: (deriv (-f)) = fun x => -deriv f x
  证明: funext fun _ => deriv.neg

Depends on / 依赖: deriv.neg
-/
theorem deriv.neg' : (deriv (-f)) = fun x => -deriv f x :=
  funext fun _ => deriv.neg

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `Neg.neg`) -/

variable (s x L)

/--
theorem `hasDerivAtFilter_neg` / 定理 `hasDerivAtFilter_neg`

English:
theorem hasDerivAtFilter_neg
  statement: HasDerivAtFilter Neg.neg (-1) L
  proof: HasDerivAtFilter.neg hasDerivAtFilter_id _

中文:
定理 hasDerivAtFilter_neg
  结论: HasDerivAtFilter Neg.neg (-1) L
  证明: HasDerivAtFilter.neg hasDerivAtFilter_id _

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.neg, hasDerivAtFilter_id
-/
theorem hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-1) L :=
HasDerivAtFilter.neg hasDerivAtFilter_id _

/--
theorem `hasDerivWithinAt_neg` / 定理 `hasDerivWithinAt_neg`

English:
theorem hasDerivWithinAt_neg
  statement: HasDerivWithinAt Neg.neg (-1) s x
  proof: hasDerivAtFilter_neg _

中文:
定理 hasDerivWithinAt_neg
  结论: HasDerivWithinAt Neg.neg (-1) s x
  证明: hasDerivAtFilter_neg _

Depends on / 依赖: hasDerivAtFilter_neg
-/
theorem hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  hasDerivAtFilter_neg _

/--
theorem `hasDerivAt_neg` / 定理 `hasDerivAt_neg`

English:
theorem hasDerivAt_neg
  statement: HasDerivAt Neg.neg (-1) x
  proof: hasDerivAtFilter_neg _

中文:
定理 hasDerivAt_neg
  结论: HasDerivAt Neg.neg (-1) x
  证明: hasDerivAtFilter_neg _

Depends on / 依赖: hasDerivAtFilter_neg
-/
theorem hasDerivAt_neg : HasDerivAt Neg.neg (-1) x :=
  hasDerivAtFilter_neg _

/--
theorem `hasDerivAt_neg'` / 定理 `hasDerivAt_neg'`

English:
theorem hasDerivAt_neg'
  statement: HasDerivAt (fun x => -x) (-1) x
  proof: hasDerivAtFilter_neg _

中文:
定理 hasDerivAt_neg'
  结论: HasDerivAt (fun x => -x) (-1) x
  证明: hasDerivAtFilter_neg _

Depends on / 依赖: hasDerivAtFilter_neg
-/
theorem hasDerivAt_neg' : HasDerivAt (fun x => -x) (-1) x :=
  hasDerivAtFilter_neg _

/--
theorem `hasStrictDerivAt_neg` / 定理 `hasStrictDerivAt_neg`

English:
theorem hasStrictDerivAt_neg
  statement: HasStrictDerivAt Neg.neg (-1) x
  proof: HasStrictDerivAt.neg hasStrictDerivAt_id _

中文:
定理 hasStrictDerivAt_neg
  结论: HasStrictDerivAt Neg.neg (-1) x
  证明: HasStrictDerivAt.neg hasStrictDerivAt_id _

Depends on / 依赖: HasStrictDerivAt, HasStrictDerivAt.neg, hasStrictDerivAt_id
-/
theorem hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-1) x :=
HasStrictDerivAt.neg hasStrictDerivAt_id _

/--
theorem `deriv_neg` / 定理 `deriv_neg`

English:
theorem deriv_neg
  statement: deriv Neg.neg x = -1
  proof: HasDerivAt.deriv (hasDerivAt_neg x)

@[simp]

中文:
定理 deriv_neg
  结论: deriv Neg.neg x = -1
  证明: HasDerivAt.deriv (hasDerivAt_neg x)

@[simp]

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, hasDerivAt_neg
-/
theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (hasDerivAt_neg x)

@[simp]
/--
theorem `deriv_neg'` / 定理 `deriv_neg'`

English:
theorem deriv_neg'
  statement: deriv (Neg.neg : 𝕜 -> 𝕜) = fun _ => -1
  proof: funext deriv_neg

@[simp]

中文:
定理 deriv_neg'
  结论: deriv (Neg.neg : 𝕜 -> 𝕜) = fun _ => -1
  证明: funext deriv_neg

@[simp]

Depends on / 依赖: deriv_neg
-/
theorem deriv_neg' : deriv (Neg.neg : 𝕜 -> 𝕜) = fun _ => -1 :=
  funext deriv_neg

@[simp]
/--
theorem `deriv_neg''` / 定理 `deriv_neg''`

English:
theorem deriv_neg''
  statement: deriv (fun x : 𝕜 => -x) x = -1
  proof: deriv_neg x

中文:
定理 deriv_neg''
  结论: deriv (fun x : 𝕜 => -x) x = -1
  证明: deriv_neg x

Depends on / 依赖: deriv_neg
-/
theorem deriv_neg'' : deriv (fun x : 𝕜 => -x) x = -1 :=
  deriv_neg x

/--
theorem `derivWithin_neg` / 定理 `derivWithin_neg`

English:
theorem derivWithin_neg
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  statement: derivWithin Neg.neg s x = -1
  proof: (hasDerivWithinAt_neg x s).derivWithin hxs

中文:
定理 derivWithin_neg
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  结论: derivWithin Neg.neg s x = -1
  证明: (hasDerivWithinAt_neg x s).derivWithin hxs

Depends on / 依赖: derivWithin, hasDerivWithinAt_neg
-/
theorem derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (hasDerivWithinAt_neg x s).derivWithin hxs

/--
theorem `differentiable_neg` / 定理 `differentiable_neg`

English:
theorem differentiable_neg
  statement: Differentiable 𝕜 (Neg.neg : 𝕜 -> 𝕜)
  proof: Differentiable.neg differentiable_id

中文:
定理 differentiable_neg
  结论: Differentiable 𝕜 (Neg.neg : 𝕜 -> 𝕜)
  证明: Differentiable.neg differentiable_id

Depends on / 依赖: Differentiable, Differentiable.neg, differentiable_id
-/
theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 -> 𝕜) :=
  Differentiable.neg differentiable_id

/--
theorem `differentiableOn_neg` / 定理 `differentiableOn_neg`

English:
theorem differentiableOn_neg
  statement: DifferentiableOn 𝕜 (Neg.neg : 𝕜 -> 𝕜) s
  proof: DifferentiableOn.neg differentiableOn_id

中文:
定理 differentiableOn_neg
  结论: DifferentiableOn 𝕜 (Neg.neg : 𝕜 -> 𝕜) s
  证明: DifferentiableOn.neg differentiableOn_id

Depends on / 依赖: DifferentiableOn, DifferentiableOn.neg, differentiableOn_id
-/
theorem differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 -> 𝕜) s :=
  DifferentiableOn.neg differentiableOn_id

/--
lemma `differentiableAt_comp_neg` / 引理 `differentiableAt_comp_neg`

English:
lemma differentiableAt_comp_neg
  given: {a : 𝕜}
  proof: by
  refine ⟨fun H => ?_, fun H => H.comp a differentiable_neg.differentiableAt⟩
  convert! ((neg_neg a).symm ▸ H).comp (-a) differentiable_neg.differentiableAt
  ext
  simp only [Function.comp_apply, neg_neg]

中文:
引理 differentiableAt_comp_neg
  条件: {a : 𝕜}
  证明: by
  refine ⟨fun H => ?_, fun H => H.comp a differentiable_neg.differentiableAt⟩
  convert! ((neg_neg a).symm ▸ H).comp (-a) differentiable_neg.differentiableAt
  ext
  simp only [Function.comp_apply, neg_neg]

Depends on / 依赖: Function, Function.comp_apply, H.comp, comp_apply, convert, differentiableAt, differentiable_neg, differentiable_neg.differentiableAt, neg_neg
-/
lemma differentiableAt_comp_neg {a : 𝕜} :
    DifferentiableAt 𝕜 (fun x => f (-x)) a ↔ DifferentiableAt 𝕜 f (-a) := by
  refine ⟨fun H => ?_, fun H => H.comp a differentiable_neg.differentiableAt⟩
  convert! ((neg_neg a).symm ▸ H).comp (-a) differentiable_neg.differentiableAt
  ext
  simp only [Function.comp_apply, neg_neg]

/--
lemma `differentiableAt_iff_comp_neg` / 引理 `differentiableAt_iff_comp_neg`

English:
lemma differentiableAt_iff_comp_neg
  given: {a : 𝕜}
  proof: by
  simp_rw [← differentiableAt_comp_neg, neg_neg]

中文:
引理 differentiableAt_iff_comp_neg
  条件: {a : 𝕜}
  证明: by
  simp_rw [← differentiableAt_comp_neg, neg_neg]

Depends on / 依赖: differentiableAt_comp_neg, neg_neg, simp_rw
-/
lemma differentiableAt_iff_comp_neg {a : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (-x)) (-a) := by
  simp_rw [← differentiableAt_comp_neg, neg_neg]

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/

@[to_fun]
/--
theorem `HasDerivAtFilter.sub` / 定理 `HasDerivAtFilter.sub`

English:
theorem HasDerivAtFilter.sub
  given: (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter g g' L)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]

中文:
定理 HasDerivAtFilter.sub
  条件: (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter g g' L)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter g g' L) :
    HasDerivAtFilter (f - g) (f' - g') L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]
/--
theorem `HasDerivWithinAt.sub` / 定理 `HasDerivWithinAt.sub`

English:
theorem HasDerivWithinAt.sub
  statement: (hf : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.sub hf hg

@[to_fun]

中文:
定理 HasDerivWithinAt.sub
  结论: (hf : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.sub hf hg

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.sub
-/
theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x :=
  HasDerivAtFilter.sub hf hg

@[to_fun]
/--
theorem `HasDerivAt.sub` / 定理 `HasDerivAt.sub`

English:
theorem HasDerivAt.sub
  given: (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
  proof: HasDerivAtFilter.sub hf hg

@[to_fun]

中文:
定理 HasDerivAt.sub
  条件: (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
  证明: HasDerivAtFilter.sub hf hg

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.sub
-/
theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f - g) (f' - g') x :=
  HasDerivAtFilter.sub hf hg

@[to_fun]
/--
theorem `HasStrictDerivAt.sub` / 定理 `HasStrictDerivAt.sub`

English:
theorem HasStrictDerivAt.sub
  given: (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
  proof: HasDerivAtFilter.sub hf hg

中文:
定理 HasStrictDerivAt.sub
  条件: (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
  证明: HasDerivAtFilter.sub hf hg

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.sub
-/
theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (f - g) (f' - g') x :=
  HasDerivAtFilter.sub hf hg

/--
theorem `derivWithin_fun_sub` / 定理 `derivWithin_fun_sub`

English:
theorem derivWithin_fun_sub
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  simp only [sub_eq_add_neg, derivWithin_fun_add hf hg.fun_neg, derivWithin.fun_neg]

中文:
定理 derivWithin_fun_sub
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  simp only [sub_eq_add_neg, derivWithin_fun_add hf hg.fun_neg, derivWithin.fun_neg]

Depends on / 依赖: derivWithin, derivWithin.fun_neg, derivWithin_fun_add, fun_neg, hg.fun_neg, sub_eq_add_neg
-/
theorem derivWithin_fun_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y - g y) s x = derivWithin f s x - derivWithin g s x := by
  simp only [sub_eq_add_neg, derivWithin_fun_add hf hg.fun_neg, derivWithin.fun_neg]

/--
theorem `derivWithin_sub` / 定理 `derivWithin_sub`

English:
theorem derivWithin_sub
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: derivWithin_fun_sub hf hg

@[simp]

中文:
定理 derivWithin_sub
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: derivWithin_fun_sub hf hg

@[simp]

Depends on / 依赖: derivWithin_fun_sub
-/
theorem derivWithin_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (f - g) s x = derivWithin f s x - derivWithin g s x :=
  derivWithin_fun_sub hf hg

@[simp]
/--
theorem `deriv_fun_sub` / 定理 `deriv_fun_sub`

English:
theorem deriv_fun_sub
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]

中文:
定理 deriv_fun_sub
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.sub, hg.hasDerivAt
-/
theorem deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y - g y) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]
/--
theorem `deriv_sub` / 定理 `deriv_sub`

English:
theorem deriv_sub
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]

中文:
定理 deriv_sub
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.sub, hg.hasDerivAt
-/
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (f - g) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]
/--
theorem `hasDerivAtFilter_sub_const_iff` / 定理 `hasDerivAtFilter_sub_const_iff`

English:
theorem hasDerivAtFilter_sub_const_iff
  given: (c : F)
  proof: hasFDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAtFilter.sub_const⟩ := hasDerivAtFilter_sub_const_iff

@[simp]

中文:
定理 hasDerivAtFilter_sub_const_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAtFilter.sub_const⟩ := hasDerivAtFilter_sub_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_sub_const_iff
-/
theorem hasDerivAtFilter_sub_const_iff (c : F) :
    HasDerivAtFilter (fun x => f x - c) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAtFilter.sub_const⟩ := hasDerivAtFilter_sub_const_iff

@[simp]
/--
theorem `hasDerivWithinAt_sub_const_iff` / 定理 `hasDerivWithinAt_sub_const_iff`

English:
theorem hasDerivWithinAt_sub_const_iff
  given: (c : F)
  proof: hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivWithinAt.sub_const⟩ := hasDerivWithinAt_sub_const_iff

@[simp]

中文:
定理 hasDerivWithinAt_sub_const_iff
  条件: (c : F)
  证明: hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivWithinAt.sub_const⟩ := hasDerivWithinAt_sub_const_iff

@[simp]

Depends on / 依赖: hasDerivAtFilter_sub_const_iff
-/
theorem hasDerivWithinAt_sub_const_iff (c : F) :
    HasDerivWithinAt (f · - c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivWithinAt.sub_const⟩ := hasDerivWithinAt_sub_const_iff

@[simp]
/--
theorem `hasDerivAt_sub_const_iff` / 定理 `hasDerivAt_sub_const_iff`

English:
theorem hasDerivAt_sub_const_iff
  given: (c : F)
  statement: HasDerivAt (f · - c) f' x ↔ HasDerivAt f f' x
  proof: hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAt.sub_const⟩ := hasDerivAt_sub_const_iff

中文:
定理 hasDerivAt_sub_const_iff
  条件: (c : F)
  结论: HasDerivAt (f · - c) f' x ↔ HasDerivAt f f' x
  证明: hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAt.sub_const⟩ := hasDerivAt_sub_const_iff

Depends on / 依赖: hasDerivAtFilter_sub_const_iff
-/
theorem hasDerivAt_sub_const_iff (c : F) : HasDerivAt (f · - c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAt.sub_const⟩ := hasDerivAt_sub_const_iff

/--
theorem `derivWithin_sub_const` / 定理 `derivWithin_sub_const`

English:
theorem derivWithin_sub_const
  given: (c : F)
  proof: by
  simp only [derivWithin, fderivWithin_sub_const]

@[simp]

中文:
定理 derivWithin_sub_const
  条件: (c : F)
  证明: by
  simp only [derivWithin, fderivWithin_sub_const]

@[simp]

Depends on / 依赖: derivWithin, fderivWithin_sub_const
-/
theorem derivWithin_sub_const (c : F) :
    derivWithin (fun y => f y - c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_sub_const]

@[simp]
/--
theorem `derivWithin_sub_const_fun` / 定理 `derivWithin_sub_const_fun`

English:
theorem derivWithin_sub_const_fun
  given: (c : F)
  statement: derivWithin (f · - c) = derivWithin f
  proof: by
  ext
  apply derivWithin_sub_const

中文:
定理 derivWithin_sub_const_fun
  条件: (c : F)
  结论: derivWithin (f · - c) = derivWithin f
  证明: by
  ext
  apply derivWithin_sub_const

Depends on / 依赖: derivWithin_sub_const
-/
theorem derivWithin_sub_const_fun (c : F) : derivWithin (f · - c) = derivWithin f := by
  ext
  apply derivWithin_sub_const

/--
theorem `deriv_sub_const` / 定理 `deriv_sub_const`

English:
theorem deriv_sub_const
  given: (c : F)
  statement: deriv (fun y => f y - c) x = deriv f x
  proof: by
  simp only [deriv, fderiv_sub_const]

@[simp]

中文:
定理 deriv_sub_const
  条件: (c : F)
  结论: deriv (fun y => f y - c) x = deriv f x
  证明: by
  simp only [deriv, fderiv_sub_const]

@[simp]

Depends on / 依赖: fderiv_sub_const
-/
theorem deriv_sub_const (c : F) : deriv (fun y => f y - c) x = deriv f x := by
  simp only [deriv, fderiv_sub_const]

@[simp]
/--
theorem `deriv_sub_const_fun` / 定理 `deriv_sub_const_fun`

English:
theorem deriv_sub_const_fun
  given: (c : F)
  statement: deriv (f · - c) = deriv f
  proof: by
  ext
  apply deriv_sub_const

中文:
定理 deriv_sub_const_fun
  条件: (c : F)
  结论: deriv (f · - c) = deriv f
  证明: by
  ext
  apply deriv_sub_const

Depends on / 依赖: deriv_sub_const
-/
theorem deriv_sub_const_fun (c : F) : deriv (f · - c) = deriv f := by
  ext
  apply deriv_sub_const

/--
theorem `HasDerivAtFilter.const_sub` / 定理 `HasDerivAtFilter.const_sub`

English:
theorem HasDerivAtFilter.const_sub
  given: (c : F) (hf : HasDerivAtFilter f f' L)
  proof: by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

中文:
定理 HasDerivAtFilter.const_sub
  条件: (c : F) (hf : HasDerivAtFilter f f' L)
  证明: by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

Depends on / 依赖: const_add, hf.neg.const_add, sub_eq_add_neg
-/
theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (fun x => c - f x) (-f') L := by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

/--
theorem `HasDerivWithinAt.const_sub` / 定理 `HasDerivWithinAt.const_sub`

English:
theorem HasDerivWithinAt.const_sub
  given: (c : F) (hf : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.const_sub c hf

中文:
定理 HasDerivWithinAt.const_sub
  条件: (c : F) (hf : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.const_sub c hf

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.const_sub, const_sub
-/
theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => c - f x) (-f') s x :=
  HasDerivAtFilter.const_sub c hf

/--
theorem `HasStrictDerivAt.const_sub` / 定理 `HasStrictDerivAt.const_sub`

English:
theorem HasStrictDerivAt.const_sub
  given: (c : F) (hf : HasStrictDerivAt f f' x)
  proof: HasDerivAtFilter.const_sub c hf

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

中文:
定理 HasStrictDerivAt.const_sub
  条件: (c : F) (hf : HasStrictDerivAt f f' x)
  证明: HasDerivAtFilter.const_sub c hf

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.const_sub, const_sub
-/
theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => c - f x) (-f') x :=
  HasDerivAtFilter.const_sub c hf

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

/--
theorem `derivWithin_const_sub` / 定理 `derivWithin_const_sub`

English:
theorem derivWithin_const_sub
  given: (c : F)
  proof: by
  simp [sub_eq_add_neg, derivWithin.fun_neg]

中文:
定理 derivWithin_const_sub
  条件: (c : F)
  证明: by
  simp [sub_eq_add_neg, derivWithin.fun_neg]

Depends on / 依赖: derivWithin, derivWithin.fun_neg, fun_neg, sub_eq_add_neg
-/
theorem derivWithin_const_sub (c : F) :
    derivWithin (fun y => c - f y) s x = -derivWithin f s x := by
  simp [sub_eq_add_neg, derivWithin.fun_neg]

/--
theorem `deriv_const_sub` / 定理 `deriv_const_sub`

English:
theorem deriv_const_sub
  given: (c : F)
  statement: deriv (c - f ·) x = -deriv f x
  proof: by
  simp only [← derivWithin_univ, derivWithin_const_sub]

@[simp]

中文:
定理 deriv_const_sub
  条件: (c : F)
  结论: deriv (c - f ·) x = -deriv f x
  证明: by
  simp only [← derivWithin_univ, derivWithin_const_sub]

@[simp]

Depends on / 依赖: derivWithin_const_sub, derivWithin_univ
-/
theorem deriv_const_sub (c : F) : deriv (c - f ·) x = -deriv f x := by
  simp only [← derivWithin_univ, derivWithin_const_sub]

@[simp]
/--
theorem `deriv_const_sub'` / 定理 `deriv_const_sub'`

English:
theorem deriv_const_sub'
  given: (c : F)
  statement: deriv (c - f ·) = (-deriv f ·)
  proof: funext fun _ => deriv_const_sub c

中文:
定理 deriv_const_sub'
  条件: (c : F)
  结论: deriv (c - f ·) = (-deriv f ·)
  证明: funext fun _ => deriv_const_sub c

Depends on / 依赖: deriv_const_sub
-/
theorem deriv_const_sub' (c : F) : deriv (c - f ·) = (-deriv f ·) :=
  funext fun _ => deriv_const_sub c

/--
theorem `deriv_const_sub_id` / 定理 `deriv_const_sub_id`

English:
theorem deriv_const_sub_id
  given: (c : 𝕜)
  statement: deriv (c - ·) x = -1
  proof: by
  rw [deriv_const_sub c]; rw [deriv_id'']

@[simp]

中文:
定理 deriv_const_sub_id
  条件: (c : 𝕜)
  结论: deriv (c - ·) x = -1
  证明: by
  rw [deriv_const_sub c]; rw [deriv_id'']

@[simp]

Depends on / 依赖: deriv_const_sub, deriv_id
-/
theorem deriv_const_sub_id (c : 𝕜) : deriv (c - ·) x = -1 := by
  rw [deriv_const_sub c]; rw [deriv_id'']

@[simp]
/--
theorem `deriv_const_sub_id'` / 定理 `deriv_const_sub_id'`

English:
theorem deriv_const_sub_id'
  given: (c : 𝕜)
  statement: deriv (c - ·) = fun _ => -1
  proof: funext fun _ => deriv_const_sub_id c

中文:
定理 deriv_const_sub_id'
  条件: (c : 𝕜)
  结论: deriv (c - ·) = fun _ => -1
  证明: funext fun _ => deriv_const_sub_id c

Depends on / 依赖: deriv_const_sub_id
-/
theorem deriv_const_sub_id' (c : 𝕜) : deriv (c - ·) = fun _ => -1 :=
  funext fun _ => deriv_const_sub_id c

/--
lemma `differentiableAt_comp_sub_const` / 引理 `differentiableAt_comp_sub_const`

English:
lemma differentiableAt_comp_sub_const
  given: {a b : 𝕜}
  proof: by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

中文:
引理 differentiableAt_comp_sub_const
  条件: {a b : 𝕜}
  证明: by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

Depends on / 依赖: differentiableAt_comp_add_const, sub_eq_add_neg
-/
lemma differentiableAt_comp_sub_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x => f (x - b)) a ↔ DifferentiableAt 𝕜 f (a - b) := by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

/--
lemma `differentiableAt_comp_const_sub` / 引理 `differentiableAt_comp_const_sub`

English:
lemma differentiableAt_comp_const_sub
  given: {a b : 𝕜}
  proof: by
  refine ⟨fun H => ?_, fun H => H.comp a (differentiable_id.const_sub _).differentiableAt⟩
  convert!
    ((sub_sub_cancel _ a).symm ▸ H).comp (b - a) (differentiable_id.const_sub _).differentiableAt
  ext
  simp

中文:
引理 differentiableAt_comp_const_sub
  条件: {a b : 𝕜}
  证明: by
  refine ⟨fun H => ?_, fun H => H.comp a (differentiable_id.const_sub _).differentiableAt⟩
  convert!
    ((sub_sub_cancel _ a).symm ▸ H).comp (b - a) (differentiable_id.const_sub _).differentiableAt
  ext
  simp

Depends on / 依赖: H.comp, const_sub, convert, differentiableAt, differentiable_id, differentiable_id.const_sub, sub_sub_cancel
-/
lemma differentiableAt_comp_const_sub {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x => f (b - x)) a ↔ DifferentiableAt 𝕜 f (b - a) := by
  refine ⟨fun H => ?_, fun H => H.comp a (differentiable_id.const_sub _).differentiableAt⟩
  convert!
    ((sub_sub_cancel _ a).symm ▸ H).comp (b - a) (differentiable_id.const_sub _).differentiableAt
  ext
  simp

/--
lemma `differentiableAt_iff_comp_sub_const` / 引理 `differentiableAt_iff_comp_sub_const`

English:
lemma differentiableAt_iff_comp_sub_const
  given: {a b : 𝕜}
  proof: by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

中文:
引理 differentiableAt_iff_comp_sub_const
  条件: {a b : 𝕜}
  证明: by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

Depends on / 依赖: differentiableAt_comp_add_const, sub_eq_add_neg
-/
lemma differentiableAt_iff_comp_sub_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (x - b)) (a + b) := by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

/--
lemma `differentiableAt_iff_comp_const_sub` / 引理 `differentiableAt_iff_comp_const_sub`

English:
lemma differentiableAt_iff_comp_const_sub
  given: {a b : 𝕜}
  proof: by
  simp [differentiableAt_comp_const_sub]

中文:
引理 differentiableAt_iff_comp_const_sub
  条件: {a b : 𝕜}
  证明: by
  simp [differentiableAt_comp_const_sub]

Depends on / 依赖: differentiableAt_comp_const_sub
-/
lemma differentiableAt_iff_comp_const_sub {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (b - x)) (b - a) := by
  simp [differentiableAt_comp_const_sub]

end Sub
