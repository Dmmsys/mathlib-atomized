/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.Defs

/-!
# Construct a `UniformSpace` from a `dist`-like function

In this file we provide a constructor for `UniformSpace`
given a `dist`-like function

## TODO

RFC: use `UniformSpace.Core.mkOfBasis`? This will change defeq here and there
-/

@[expose] public section

open Filter Set
open scoped Uniformity

variable {X M : Type*}

namespace UniformSpace

/-- Define a `UniformSpace` using a "distance" function. The function can be, e.g., the
distance in a (usual or extended) metric space or an absolute value on a ring. -/
@[instance_reducible]
/-
**UniformSpace.ofFun** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`。
形式化陈述：ofFun [AddCommMonoid M] [PartialOrder M] (d : X -> X -> M) (refl : forall 
x, d x x = 0) (symm : forall x y, d x y = d y x) (triangle : forall x y z, d x z
 <= d x y + d y z) (half : forall ε > (0 : M), exists δ > (0 : M), forall x < δ,
 forall y < δ, x + y < ε) : UniformSpace X
参数：d : X -> X -> M；refl : forall x, d x x = 0；symm : forall x y, d x y = d y x；t
riangle : forall x y z, d x z <= d x y + d y z；half : forall ε > (0 : M), exists
 δ > (0 : M), forall x < δ, forall y < δ, x + y < ε。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a `UniformSpace` using a "distance" function. The function can be, e.g., 
the
distance in a (usual or extended) metric space or an absolute value on a ring.
-/
def ofFun [AddCommMonoid M] [PartialOrder M]
    (d : X → X → M) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε) :
    UniformSpace X :=
  .ofCore
    { uniformity := ⨅ r > 0, 𝓟 { x | d x.1 x.2 < r }
      refl := le_iInf₂ fun r hr => principal_mono.2 <| by simp [Set.subset_def, *]
      symm := tendsto_iInf_iInf fun r => tendsto_iInf_iInf fun _ => tendsto_principal_principal.2
        fun x hx => by rwa [mem_ofPred, symm]
      comp := le_iInf₂ fun r hr => let ⟨δ, h0, hδr⟩ := half r hr; le_principal_iff.2 <|
        mem_of_superset
          (mem_lift' <| mem_iInf_of_mem δ <| mem_iInf_of_mem h0 <| mem_principal_self _)
          fun (x, z) ⟨y, h₁, h₂⟩ => (triangle _ _ _).trans_lt (hδr _ h₁ _ h₂) }
/-
**UniformSpace.hasBasis_ofFun** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：hasBasis_ofFun [AddCommMonoid M] [LinearOrder M] (h₀ : exists x : M, 0 < x
) (d : X -> X -> M) (refl : forall x, d x x = 0) (symm : forall x y, d x y = d y
 x) (triangle : forall x y z, d x z <= d x y + d y z) (half : forall ε > (0 : M)
, exists δ > (0 : M), forall x < δ, forall y < δ, x + y < ε) : 𝓤[.ofFun d refl s
ymm triangle half].HasBasis ((0 : M) < ·) (fun ε => { x | d x.1 x.2 < ε })
参数：h₀ : exists x : M, 0 < x；d : X -> X -> M；refl : forall x, d x x = 0；symm : fo
rall x y, d x y = d y x；triangle : forall x y z, d x z <= d x y + d y z；half : f
orall ε > (0 : M), exists δ > (0 : M), forall x < δ, forall y < δ, x + y < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_biInf_principal'`：hasBasis_biInf_principal' {ι : Type*} 
{p : ι -> Prop} {s : ι -> Set α} (h : forall i, p i -> forall j, p j -> exists k
, p k ∧ s k subseteq s…
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem hasBasis_ofFun [AddCommMonoid M] [LinearOrder M]
    (h₀ : ∃ x : M, 0 < x) (d : X → X → M) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε) :
    𝓤[.ofFun d refl symm triangle half].HasBasis ((0 : M) < ·) (fun ε => { x | d x.1 x.2 < ε }) :=
  hasBasis_biInf_principal'
    (fun ε₁ h₁ ε₂ h₂ => ⟨min ε₁ ε₂, lt_min h₁ h₂, fun _x hx => lt_of_lt_of_le hx (min_le_left _ _),
      fun _x hx => lt_of_lt_of_le hx (min_le_right _ _)⟩) h₀

open scoped Topology in
/-- Define a `UniformSpace` using a "distance" function. The function can be, e.g., the
distance in a (usual or extended) metric space or an absolute value on a ring. We assume that
there is a preexisting topology, for which the neighborhoods can be expressed using the "distance",
and we make sure that the uniform space structure we construct has a topology which is defeq
to the original one. -/
@[instance_reducible]
/-
**UniformSpace.ofFunOfHasBasis** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`。
形式化陈述：ofFunOfHasBasis [t : TopologicalSpace X] [AddCommMonoid M] [LinearOrder M]
 (d : X -> X -> M) (refl : forall x, d x x = 0) (symm : forall x y, d x y = d y 
x) (triangle : forall x y z, d x z <= d x y + d y z) (half : forall ε > (0 : M),
 exists δ > (0 : M), forall x < δ, forall y < δ, x + y < ε) (basis : forall x, (
𝓝 x).HasBasis (fun ε => 0 < ε) (fun ε => {y | d x y < ε})) : UniformSpace X wher
e toTopologicalSpace
参数：d : X -> X -> M；refl : forall x, d x x = 0；symm : forall x y, d x y = d y x；t
riangle : forall x y z, d x z <= d x y + d y z；half : forall ε > (0 : M), exists
 δ > (0 : M), forall x < δ, forall y < δ, x + y < ε；basis : forall x, (𝓝 x).HasB
asis (fun ε => 0 < ε) (fun ε => {y | d x y < ε})。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.symm`：∀ {α : Type u} [self : UniformSpace α], Filter.Tendst
o Prod.swap UniformSpace.uniformity UniformSpace.uniformity
· 使用定理 `UniformSpace.comp`：∀ {α : Type u} [self : UniformSpace α],   (UniformSpa
ce.uniformity.lift' fun s => SetRel.comp s s) ≤ UniformSpace.uniformity

--- 原说明 ---
Define a `UniformSpace` using a "distance" function. The function can be, e.g., 
the
distance in a (usual or extended) metric space or an absolute value on a ring. W
e assume that
there is a preexisting topology, for which the neighborhoods can be expressed us
ing the "distance",
and we make sure that the uniform space structure we construct has a topology wh
ich is defeq
to the original one.
-/
def ofFunOfHasBasis [t : TopologicalSpace X] [AddCommMonoid M] [LinearOrder M]
    (d : X → X → M) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε)
    (basis : ∀ x, (𝓝 x).HasBasis (fun ε ↦ 0 < ε) (fun ε ↦ {y | d x y < ε})) :
    UniformSpace X where
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x :=
    (basis x).eq_of_same_basis <|
      (hasBasis_ofFun (basis x).ex_mem d refl symm triangle half).comap (Prod.mk x)
  __ := ofFun d refl symm triangle half

end UniformSpace

