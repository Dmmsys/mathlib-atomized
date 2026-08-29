/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Operator.Conformal

/-!
# Conformal Maps

A continuous linear map between real normed spaces `X` and `Y` is `ConformalAt` some point `x`
if it is real differentiable at that point and its differential is a conformal linear map.

## Main definitions

* `ConformalAt`: the main definition of conformal maps
* `Conformal`: maps that are conformal at every point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformalAt_iff_isConformalMap_fderiv`: an equivalent definition of the conformality of a map

In `Analysis.Calculus.Conformal.InnerProduct`:
* `conformalAt_iff`: an equivalent definition of the conformality of a map

In `Geometry.Euclidean.Angle.Unoriented.Conformal`:
* `ConformalAt.preserves_angle`: if a map is conformal at `x`, then its differential preserves
  all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/

@[expose] public section


noncomputable section

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace Real X] [NormedSpace Real Y] [NormedSpace Real Z]

section LocConformality

open LinearIsometry ContinuousLinearMap

/--
Definition of `ConformalAt` / `ConformalAt` 的定义

English:
definition ConformalAt
  signature: (f : X -> Y) (x : X)
  body: exists f' : X ->L[Real] Y, HasFDerivAt f f' x ∧ IsConformalMap f'

中文:
定义 ConformalAt
  签名: (f : X -> Y) (x : X)
  定义体: exists f' : X ->L[Real] Y, HasFDerivAt f f' x ∧ IsConformalMap f'

Depends on / 依赖: HasFDerivAt, IsConformalMap
-/
def ConformalAt (f : X -> Y) (x : X) :=
  exists f' : X ->L[Real] Y, HasFDerivAt f f' x ∧ IsConformalMap f'

/--
theorem `conformalAt_id` / 定理 `conformalAt_id`

English:
theorem conformalAt_id
  given: (x : X)
  statement: ConformalAt _root_.id x
  proof: ⟨.id Real X, hasFDerivAt_id _, isConformalMap_id⟩

中文:
定理 conformalAt_id
  条件: (x : X)
  结论: ConformalAt _root_.id x
  证明: ⟨.id Real X, hasFDerivAt_id _, isConformalMap_id⟩

Depends on / 依赖: hasFDerivAt_id, isConformalMap_id
-/
theorem conformalAt_id (x : X) : ConformalAt _root_.id x :=
  ⟨.id Real X, hasFDerivAt_id _, isConformalMap_id⟩

/--
theorem `conformalAt_const_smul` / 定理 `conformalAt_const_smul`

English:
theorem conformalAt_const_smul
  given: {c : Real} (h : c != 0) (x : X)
  statement: ConformalAt (fun x' : X => c • x') x
  proof: ⟨c • ContinuousLinearMap.id Real X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩

@[nontriviality]

中文:
定理 conformalAt_const_smul
  条件: {c : 实数} (h : c != 0) (x : X)
  结论: ConformalAt (fun x' : X => c • x') x
  证明: ⟨c • ContinuousLinearMap.id Real X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩

@[nontriviality]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, const_smul, hasFDerivAt_id, isConformalMap_const_smul
-/
theorem conformalAt_const_smul {c : Real} (h : c != 0) (x : X) : ConformalAt (fun x' : X => c • x') x :=
  ⟨c • ContinuousLinearMap.id Real X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩

@[nontriviality]
/--
theorem `Subsingleton.conformalAt` / 定理 `Subsingleton.conformalAt`

English:
theorem Subsingleton.conformalAt
  given: [Subsingleton X] (f : X -> Y) (x : X)
  statement: ConformalAt f x
  proof: ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩

中文:
定理 子单例.conformalAt
  条件: [子单例 X] (f : X -> Y) (x : X)
  结论: ConformalAt f x
  证明: ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩

Depends on / 依赖: hasFDerivAt_of_subsingleton, isConformalMap_of_subsingleton
-/
theorem Subsingleton.conformalAt [Subsingleton X] (f : X -> Y) (x : X) : ConformalAt f x :=
  ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩

/--
theorem `conformalAt_iff_isConformalMap_fderiv` / 定理 `conformalAt_iff_isConformalMap_fderiv`

English:
theorem conformalAt_iff_isConformalMap_fderiv
  given: {f : X -> Y} {x : X}
  proof: by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt Real f x
    · exact ⟨fderiv Real f x, h.hasFDerivAt, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero

中文:
定理 conformalAt_iff_isConformalMap_fderiv
  条件: {f : X -> Y} {x : X}
  证明: by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt Real f x
    · exact ⟨fderiv Real f x, h.hasFDerivAt, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero

Depends on / 依赖: DifferentiableAt, H.ne_zero, absurd, fderiv, fderiv_zero_of_not_differentiableAt, h.hasFDerivAt, hasFDerivAt, hf.fderiv, ne_zero, nontriviality
-/
theorem conformalAt_iff_isConformalMap_fderiv {f : X -> Y} {x : X} :
    ConformalAt f x ↔ IsConformalMap (fderiv Real f x) := by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt Real f x
    · exact ⟨fderiv Real f x, h.hasFDerivAt, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero

namespace ConformalAt

/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  given: {f : X -> Y} {x : X} (h : ConformalAt f x)
  statement: DifferentiableAt Real f x
  proof: let ⟨_, h₁, _⟩ := h
  h₁.differentiableAt

中文:
定理 differentiableAt
  条件: {f : X -> Y} {x : X} (h : ConformalAt f x)
  结论: DifferentiableAt 实数 f x
  证明: let ⟨_, h₁, _⟩ := h
  h₁.differentiableAt

Depends on / 依赖: differentiableAt
-/
theorem differentiableAt {f : X -> Y} {x : X} (h : ConformalAt f x) : DifferentiableAt Real f x :=
  let ⟨_, h₁, _⟩ := h
  h₁.differentiableAt

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: {f g : X -> Y} {x : X} {u : Set X} (hx : x in u) (hu : IsOpen u) (hf : ConformalAt f x)
  proof: let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩

中文:
定理 congr
  结论: {f g : X -> Y} {x : X} {u : 集合 X} (hx : x in u) (hu : 是开集 u) (hf : ConformalAt f x)
  证明: let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩

Depends on / 依赖: congr_of_eventuallyEq, eventually_mem, hfderiv, hfderiv.congr_of_eventuallyEq, hu.eventually_mem
-/
theorem congr {f g : X -> Y} {x : X} {u : Set X} (hx : x in u) (hu : IsOpen u) (hf : ConformalAt f x)
    (h : forall x : X, x in u -> g x = f x) : ConformalAt g x :=
  let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {f : X -> Y} {g : Y -> Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x)
  proof: by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩

中文:
定理 comp
  条件: {f : X -> Y} {g : Y -> Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x)
  证明: by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩

Depends on / 依赖: cg.comp
-/
theorem comp {f : X -> Y} {g : Y -> Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
    ConformalAt (g ∘ f) x := by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩

/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  given: {f : X -> Y} {x : X} {c : Real} (hc : c != 0) (hf : ConformalAt f x)
  proof: (conformalAt_const_smul hc <| f x).comp x hf

中文:
定理 const_smul
  条件: {f : X -> Y} {x : X} {c : 实数} (hc : c != 0) (hf : ConformalAt f x)
  证明: (conformalAt_const_smul hc <| f x).comp x hf

Depends on / 依赖: conformalAt_const_smul
-/
theorem const_smul {f : X -> Y} {x : X} {c : Real} (hc : c != 0) (hf : ConformalAt f x) :
    ConformalAt (c • f) x :=
  (conformalAt_const_smul hc <| f x).comp x hf

end ConformalAt

end LocConformality

section GlobalConformality

/--
Definition of `Conformal` / `Conformal` 的定义

English:
definition Conformal
  signature: (f : X -> Y)
  body: forall x : X, ConformalAt f x

中文:
定义 共形
  签名: (f : X -> Y)
  定义体: forall x : X, ConformalAt f x

Depends on / 依赖: ConformalAt
-/
def Conformal (f : X -> Y) :=
  forall x : X, ConformalAt f x

/--
theorem `conformal_id` / 定理 `conformal_id`

English:
theorem conformal_id
  statement: Conformal (id : X -> X)
  proof: fun x => conformalAt_id x

中文:
定理 conformal_id
  结论: 共形 (id : X -> X)
  证明: fun x => conformalAt_id x

Depends on / 依赖: conformalAt_id
-/
theorem conformal_id : Conformal (id : X -> X) := fun x => conformalAt_id x

/--
theorem `conformal_const_smul` / 定理 `conformal_const_smul`

English:
theorem conformal_const_smul
  given: {c : Real} (h : c != 0)
  statement: Conformal fun x : X => c • x
  proof: fun x =>
  conformalAt_const_smul h x

中文:
定理 conformal_const_smul
  条件: {c : 实数} (h : c != 0)
  结论: 共形 fun x : X => c • x
  证明: fun x =>
  conformalAt_const_smul h x
-/
theorem conformal_const_smul {c : Real} (h : c != 0) : Conformal fun x : X => c • x := fun x =>
  conformalAt_const_smul h x

namespace Conformal

/--
theorem `conformalAt` / 定理 `conformalAt`

English:
theorem conformalAt
  given: {f : X -> Y} (h : Conformal f) (x : X)
  statement: ConformalAt f x
  proof: h x

中文:
定理 conformalAt
  条件: {f : X -> Y} (h : 共形 f) (x : X)
  结论: ConformalAt f x
  证明: h x
-/
theorem conformalAt {f : X -> Y} (h : Conformal f) (x : X) : ConformalAt f x :=
  h x

/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  given: {f : X -> Y} (h : Conformal f)
  statement: Differentiable Real f
  proof: fun x =>
  (h x).differentiableAt

中文:
定理 differentiable
  条件: {f : X -> Y} (h : 共形 f)
  结论: 可微 实数 f
  证明: fun x =>
  (h x).differentiableAt
-/
theorem differentiable {f : X -> Y} (h : Conformal f) : Differentiable Real f := fun x =>
  (h x).differentiableAt

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {f : X -> Y} {g : Y -> Z} (hf : Conformal f) (hg : Conformal g)
  statement: Conformal (g ∘ f)
  proof: fun x => (hg <| f x).comp x (hf x)

中文:
定理 comp
  条件: {f : X -> Y} {g : Y -> Z} (hf : 共形 f) (hg : 共形 g)
  结论: 共形 (g ∘ f)
  证明: fun x => (hg <| f x).comp x (hf x)
-/
theorem comp {f : X -> Y} {g : Y -> Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
  fun x => (hg <| f x).comp x (hf x)

/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  given: {f : X -> Y} (hf : Conformal f) {c : Real} (hc : c != 0)
  statement: Conformal (c • f)
  proof: fun x => (hf x).const_smul hc

中文:
定理 const_smul
  条件: {f : X -> Y} (hf : 共形 f) {c : 实数} (hc : c != 0)
  结论: 共形 (c • f)
  证明: fun x => (hf x).const_smul hc

Depends on / 依赖: const_smul
-/
theorem const_smul {f : X -> Y} (hf : Conformal f) {c : Real} (hc : c != 0) : Conformal (c • f) :=
  fun x => (hf x).const_smul hc

end Conformal

end GlobalConformality
