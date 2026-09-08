/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

/-!
# Diffeomorphisms

This file implements diffeomorphisms.

## Definitions

* `Diffeomorph I I' M M' n`: `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞` or `n = ω`; we use notation instead.
* `Diffeomorph.toHomeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `ContinuousLinearEquiv.toDiffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `ModelWithCorners.transContinuousLinearEquiv`: compose a given `ModelWithCorners` with a
  continuous linear equiv between the old and the new target spaces. Useful, e.g, to turn any
  finite-dimensional manifold into a manifold modelled on a Euclidean space.
* `Diffeomorph.toTransContinuousLinearEquiv`: the identity diffeomorphism between `M` with
  model `I` and `M` with model `I.transContinuousLinearEquiv e`.

This file also provides diffeomorphisms related to products and disjoint unions.
* `Diffeomorph.prodCongr`: the product of two diffeomorphisms
* `Diffeomorph.prodComm`: `M × N` is diffeomorphic to `N × M`
* `Diffeomorph.prodAssoc`: `(M × N) × N'` is diffeomorphic to `M × (N × N')`
* `Diffeomorph.sumCongr`: the disjoint union of two diffeomorphisms
* `Diffeomorph.sumComm`: `M ⊕ M'` is diffeomorphic to `M' × M`
* `Diffeomorph.sumAssoc`: `(M ⊕ N) ⊕ P` is diffeomorphic to `M ⊕ (N ⊕ P)`
* `Diffeomorph.sumEmpty`: `M ⊕ ∅` is diffeomorphic to `M`

## Notation

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `Diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `Diffeomorph I J M N ∞`
* `E ≃ₘ^n[𝕜] E'`     := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'`       := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/

@[expose] public section


open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H] {H' : Type*}
  [TopologicalSpace H'] {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {N' : Type*}
  [TopologicalSpace N'] [ChartedSpace G' N'] {n : ℕ∞ω}

section Defs

variable (I I' M M' n)

/-- `n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to `I`
and `I'`, denoted as `M ≃ₘ^n⟮I, I'⟯ M'` (in the `Manifold` namespace). -/
/-
**Diffeomorph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {E' : Type u_3} →             [inst_3 : NormedAddCommGroup E'] →      
         [inst_4 : NormedSpace 𝕜 E'] →                 {H : Type u_5} →         
          [inst_5 : TopologicalSpace H] →                     {H' : Type u_6} → 
                      [inst_6 : TopologicalSpace H'] →                         M
odelWithCorners 𝕜 E H →                           ModelWithCorners 𝕜 E' H' →    
                         (M : Type u_9) →                               [inst : 
TopologicalSpace M] →                                 [ChartedSpace H M] →      
                             (M' : Type u_10) →                                 
    [inst : TopologicalSpace M'] →                                       [Charte
dSpace H' M'] → WithTop ℕ∞ → Type (max u_10 u_9)
参数：M : Type u_9；M' : Type u_10；max u_10 u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n`-times continuously differentiable diffeomorphism between `M` and `M'` with r
espect to `I`
and `I'`, denoted as `M ≃ₘ^n⟮I, I'⟯ M'` (in the `Manifold` namespace).
-/
structure Diffeomorph extends M ≃ M' where
  protected contMDiff_toFun : CMDiff n toEquiv
  protected contMDiff_invFun : CMDiff n toEquiv.symm


end Defs

@[inherit_doc]
scoped[Manifold] notation M " ≃ₘ^" n:1000 "⟮" I ", " J "⟯ " N => Diffeomorph I J M N n

/-- Infinitely differentiable diffeomorphism between `M` and `M'` with respect to `I` and `I'`. -/
scoped[Manifold] notation M " ≃ₘ⟮" I ", " J "⟯ " N => Diffeomorph I J M N ∞

-- Porting note: this notation is broken because `n[𝕜]` gets parsed as `getElem`
/-- `n`-times continuously differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' n

/-- Infinitely differentiable diffeomorphism between `E` and `E'`. -/
scoped[Manifold] notation3 E " ≃ₘ[" 𝕜 "] " E' => Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' ∞

namespace Diffeomorph

/-
**Diffeomorph.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞},   Function.Injective
 Diffeomorph.toEquiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toEquiv_injective : Injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I, I'⟯ M') → M ≃ M')
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
/-
**Diffeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (M ≃ₘ^n⟮I, I'⟯ M') M M' where
  coe Φ := Φ.toEquiv
  inv Φ := Φ.toEquiv.symm
  left_inv Φ := Φ.left_inv
  right_inv Φ := Φ.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h

/-- Interpret a diffeomorphism as a `ContMDiffMap`. -/
@[coe]
/-
**Diffeomorph.toContMDiffMap** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：toContMDiffMap (Φ : M ≃ₘ^n⟮I, I'⟯ M') : C^n⟮I, M; I', M'⟯
参数：Φ : M ≃ₘ^n⟮I, I'⟯ M'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiff_toFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {E' : Type u…

--- 原说明 ---
Interpret a diffeomorphism as a `ContMDiffMap`.
-/
def toContMDiffMap (Φ : M ≃ₘ^n⟮I, I'⟯ M') : C^n⟮I, M; I', M'⟯ :=
  ⟨Φ, Φ.contMDiff_toFun⟩
/-
**Diffeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ :=
  ⟨toContMDiffMap⟩

@[continuity]
/-
**Diffeomorph.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (h : Diffeomorph I 
I' M M' n), Continuous ⇑h
参数：h : Diffeomorph I I' M M' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `Diffeomorph.contMDiff_toFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {E' : Type u…
-/
protected theorem continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : Continuous h :=
  h.contMDiff_toFun.continuous
/-
**Diffeomorph.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (h : Diffeomorph I 
I' M M' n), ContMDiff I I' n ⇑h
参数：h : Diffeomorph I I' M M' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiff_toFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {E' : Type u…
-/
protected theorem contMDiff (h : M ≃ₘ^n⟮I, I'⟯ M') : CMDiff n h :=
  h.contMDiff_toFun
/-
**Diffeomorph.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (h : Diffeomorph I 
I' M M' n) {x : M}, ContMDiffAt I I' n (⇑h) x
参数：h : Diffeomorph I I' M M' n；⇑h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `Diffeomorph.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
E' : Type u…
-/
protected theorem contMDiffAt (h : M ≃ₘ^n⟮I, I'⟯ M') {x} : CMDiffAt n h x :=
  h.contMDiff.contMDiffAt
/-
**Diffeomorph.contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (h : Diffeomorph I 
I' M M' n) {s : Set M} {x : M}, ContMDiffWithinAt I I' n (⇑h) s x
参数：h : Diffeomorph I I' M M' n；⇑h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Diffeomorph.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {E' : Type u…
-/
protected theorem contMDiffWithinAt (h : M ≃ₘ^n⟮I, I'⟯ M') {s x} : CMDiffAt[s] n h x :=
  h.contMDiffAt.contMDiffWithinAt
/-
**Diffeomorph.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   {n : WithTop ℕ∞} (h : Diffe
omorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' n), ContDiff 
𝕜 n ⇑h
参数：h : Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' n
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…
· 使用定理 `Diffeomorph.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
E' : Type u…
-/
protected theorem contDiff (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E') : ContDiff 𝕜 n h :=
  h.contMDiff.contDiff
/-
**Diffeomorph.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (h : Diffeomorph I 
I' M M' n), n ≠ 0 → MDiff ⇑h
参数：h : Diffeomorph I I' M M' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `Diffeomorph.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
E' : Type u…
-/
protected theorem mdifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0) : MDiff h :=
  h.contMDiff.mdifferentiable hn
/-
**Diffeomorph.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_5}   [inst_5 : To
pologicalSpace H] {H' : Type u_6} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_9} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_10} [inst_9 : Topologica
lSpace M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (h : Diffeomorph I 
I' M M' n) (s : Set M), n ≠ 0 → MDiff[s] ⇑h
参数：h : Diffeomorph I I' M M' n；s : Set M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `Diffeomorph.mdifferentiable`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {E' : Type u…
-/
protected theorem mdifferentiableOn (h : M ≃ₘ^n⟮I, I'⟯ M') (s : Set M) (hn : n ≠ 0) : MDiff[s] h :=
  (h.mdifferentiable hn).mdifferentiableOn

@[simp]
/-
**Diffeomorph.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_toEquiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.toEquiv = h
参数：h : M ≃ₘ^n⟮I, I'⟯ M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.toEquiv = h :=
  rfl

@[simp, norm_cast]
/-
**Diffeomorph.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h
参数：h : M ≃ₘ^n⟮I, I'⟯ M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h :=
  rfl

@[simp]
/-
**Diffeomorph.toEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：toEquiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.toEquiv = h'.toEquiv ↔ h = h'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Diffeomorph.toEquiv_injective`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {E' : Type u…
-/
theorem toEquiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  toEquiv_injective.eq_iff

/-- Coercion to function `fun h : M ≃ₘ^n⟮I, I'⟯ M' ↦ (h : M → M')` is injective. -/
/-
**Diffeomorph.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coeFn_injective : Injective ((↑) : (M ≃ₘ^n⟮I, I'⟯ M') -> (M -> M'))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
Coercion to function `fun h : M ≃ₘ^n⟮I, I'⟯ M' ↦ (h : M → M')` is injective.
-/
theorem coeFn_injective : Injective ((↑) : (M ≃ₘ^n⟮I, I'⟯ M') → (M → M')) :=
  DFunLike.coe_injective

@[ext]
/-
**Diffeomorph.ext** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h' x) : h = h'
参数：Heq : forall x, h x = h' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.coeFn_injective`：coeFn_injective : Injective ((↑) : (M ≃ₘ^n⟮
I, I'⟯ M') -> (M -> M'))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
  coeFn_injective <| funext Heq
/-
**Diffeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMapClass (M ≃ₘ⟮I, J⟯ N) M N where
  map_continuous f := f.continuous

section

variable (M I n)

/-- Identity map as a diffeomorphism. -/
/-
**Diffeomorph.refl** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_5} →             [inst_3 : TopologicalSpace H] →          
     (I : ModelWithCorners 𝕜 E H) →                 (M : Type u_9) →            
       [inst_4 : TopologicalSpace M] → [inst_5 : ChartedSpace H M] → (n : WithTo
p ℕ∞) → Diffeomorph I I M M n
参数：I : ModelWithCorners 𝕜 E H；M : Type u_9；n : WithTop ℕ∞。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)

--- 原说明 ---
Identity map as a diffeomorphism.
-/
protected def refl : M ≃ₘ^n⟮I, I⟯ M where
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id
  toEquiv := Equiv.refl M

@[simp]
/-
**Diffeomorph.refl_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：refl_toEquiv : (Diffeomorph.refl I M n).toEquiv = Equiv.refl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toEquiv : (Diffeomorph.refl I M n).toEquiv = Equiv.refl _ :=
  rfl

@[simp]
/-
**Diffeomorph.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_refl : ⇑(Diffeomorph.refl I M n) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(Diffeomorph.refl I M n) = id :=
  rfl

end

/-- Composition of two diffeomorphisms. -/
@[trans]
/-
**Diffeomorph.trans** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {E' : Type u_3} →             [inst_3 : NormedAddCommGroup E'] →      
         [inst_4 : NormedSpace 𝕜 E'] →                 {F : Type u_4} →         
          [inst_5 : NormedAddCommGroup F] →                     [inst_6 : Normed
Space 𝕜 F] →                       {H : Type u_5} →                         [ins
t_7 : TopologicalSpace H] →                           {H' : Type u_6} →         
                    [inst_8 : TopologicalSpace H'] →                            
   {G : Type u_7} →                                 [inst_9 : TopologicalSpace G
] →                                   {I : ModelWithCorners 𝕜 E H} →            
                         {I' : ModelWithCorners 𝕜 E' H'} →                      
                 {J : ModelWithCorners 𝕜 F G} →                                 
        {M : Type u_9} →                                           [inst_10 : To
pologicalSpace M] →                                             [inst_11 : Chart
edSpace H M] →                                               {M' : Type u_10} → 
                                                [inst_12 : TopologicalSpace M'] 
→                                                   [inst_13 : ChartedSpace H' M
'] →                                                     {N : Type u_11} →      
                                                 [inst_14 : TopologicalSpace N] 
→                                                         [inst_15 : ChartedSpac
e G N] →                                                           {n : WithTop 
ℕ∞} →                                                             Diffeomorph I 
I' M M' n →                                                               Diffeo
morph I' J M' N n → Diffeomorph I J M N n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of two diffeomorphisms.
-/
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : M ≃ₘ^n⟮I, J⟯ N where
  contMDiff_toFun := h₂.contMDiff.comp h₁.contMDiff
  contMDiff_invFun := h₁.contMDiff_invFun.comp h₂.contMDiff_invFun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]
/-
**Diffeomorph.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h
参数：h : M ≃ₘ^n⟮I, I'⟯ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.ext`：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h'
 x) : h = h'
-/
theorem trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext fun _ => rfl

@[simp]
/-
**Diffeomorph.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (Diffeomorph.refl I M n).trans h = h
参数：h : M ≃ₘ^n⟮I, I'⟯ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.ext`：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h'
 x) : h = h'
-/
theorem refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext fun _ => rfl

@[simp]
/-
**Diffeomorph.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : ⇑(h₁.trans h₂)
 = h₂ ∘ h₁
参数：h₁ : M ≃ₘ^n⟮I, I'⟯ M'；h₂ : M' ≃ₘ^n⟮I', J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl

/-- Inverse of a diffeomorphism. -/
@[symm]
/-
**Diffeomorph.symm** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_4} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H : Type u_5} →            
       [inst_5 : TopologicalSpace H] →                     {G : Type u_7} →     
                  [inst_6 : TopologicalSpace G] →                         {I : M
odelWithCorners 𝕜 E H} →                           {J : ModelWithCorners 𝕜 F G} 
→                             {M : Type u_9} →                               [in
st_7 : TopologicalSpace M] →                                 [inst_8 : ChartedSp
ace H M] →                                   {N : Type u_11} →                  
                   [inst_9 : TopologicalSpace N] →                              
         [inst_10 : ChartedSpace G N] →                                         
{n : WithTop ℕ∞} → Diffeomorph I J M N n → Diffeomorph J I N M n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Diffeomorph.contMDiff_invFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {E' : Type u…
· 使用定理 `Diffeomorph.contMDiff_toFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {E' : Type u…

--- 原说明 ---
Inverse of a diffeomorphism.
-/
protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M where
  contMDiff_toFun := h.contMDiff_invFun
  contMDiff_invFun := h.contMDiff_toFun
  toEquiv := h.toEquiv.symm

@[simp]
/-
**Diffeomorph.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : N) : h (h.symm x) = x
参数：h : M ≃ₘ^n⟮I, J⟯ N；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : N) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
/-
**Diffeomorph.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : M) : h.symm (h x) = x
参数：h : M ≃ₘ^n⟮I, J⟯ N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : M) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
/-
**Diffeomorph.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.ext`：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h'
 x) : h = h'
-/
theorem symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n :=
  ext fun _ => rfl

@[simp]
/-
**Diffeomorph.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：self_trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = Diffeomorph.refl I
 M n
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.ext`：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h'
 x) : h = h'
· 使用定理 `Diffeomorph.symm_apply_apply`：symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x :
 M) : h.symm (h x) = x
-/
theorem self_trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = Diffeomorph.refl I M n :=
  ext h.symm_apply_apply

@[simp]
/-
**Diffeomorph.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_trans_self (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = Diffeomorph.refl J
 N n
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.ext`：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h'
 x) : h = h'
· 使用定理 `Diffeomorph.apply_symm_apply`：apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x :
 N) : h (h.symm x) = x
-/
theorem symm_trans_self (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = Diffeomorph.refl J N n :=
  ext h.apply_symm_apply

@[simp]
/-
**Diffeomorph.symm_trans'** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : (h₁.trans h₂
).symm = h₂.symm.trans h₁.symm
参数：h₁ : M ≃ₘ^n⟮I, I'⟯ M'；h₂ : M' ≃ₘ^n⟮I', J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
    (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl

@[simp]
/-
**Diffeomorph.symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toEquiv = h.toEquiv.symm
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toEquiv = h.toEquiv.symm :=
  rfl

@[simp, mfld_simps]
/-
**Diffeomorph.toEquiv_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：toEquiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toEquiv.symm = h.symm
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toEquiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toEquiv.symm = h.symm :=
  rfl
/-
**Diffeomorph.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：image_eq_preimage_symm (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h '' s = h.symm 
⁻¹' s
参数：h : M ≃ₘ^n⟮I, J⟯ N；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_eq_preimage_symm (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage_symm s
/-
**Diffeomorph.symm_image_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h.symm '' s = h 
⁻¹' s
参数：h : M ≃ₘ^n⟮I, J⟯ N；s : Set N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.image_eq_preimage_symm`：image_eq_preimage_symm (h : M ≃ₘ^n⟮I
, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s
-/
theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage_symm s

@[simp, mfld_simps]
nonrec theorem range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α → M) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp, image_eq_preimage_symm]

@[simp]
/-
**Diffeomorph.image_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：image_symm_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h '' h.symm '' s = s
参数：h : M ≃ₘ^n⟮I, J⟯ N；s : Set N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
-/
theorem image_symm_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set N) : h '' h.symm '' s = s :=
  h.toEquiv.image_symm_image s

@[simp]
/-
**Diffeomorph.symm_image_image** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h.symm '' h '' s = s
参数：h : M ≃ₘ^n⟮I, J⟯ N；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) : h.symm '' h '' s = s :=
  h.toEquiv.symm_image_image s

/-- A diffeomorphism is a homeomorphism. -/
/-
**Diffeomorph.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : M ≃ₜ N
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…

--- 原说明 ---
A diffeomorphism is a homeomorphism.
-/
def toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : M ≃ₜ N :=
  ⟨h.toEquiv, h.continuous, h.symm.continuous⟩

@[simp]
/-
**Diffeomorph.toHomeomorph_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：toHomeomorph_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.toHomeomorph.toEquiv = h.toE
quiv
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_toEquiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.toHomeomorph.toEquiv = h.toEquiv :=
  rfl

@[simp]
/-
**Diffeomorph.symm_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：symm_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toHomeomorph = h.toHomeomo
rph.symm
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.toHomeomorph = h.toHomeomorph.symm :=
  rfl

@[simp]
/-
**Diffeomorph.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph = h
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
/-
**Diffeomorph.coe_toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_toHomeomorph_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph.symm = h.symm
参数：h : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl

@[simp]
/-
**Diffeomorph.contMDiffWithinAt_comp_diffeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Diffeomorph`。
形式化陈述：contMDiffWithinAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> 
M'} {s x} (hm : m <= n) : CMDiffAt[s] m (f ∘ h) x ↔ CMDiffAt[h.symm ⁻¹' s] m f (
h x)
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Diffeomorph.apply_symm_apply`：apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x :
 N) : h (h.symm x) = x
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Diffeomorph.symm_apply_apply`：symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x :
 M) : h.symm (h x) = x
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `Diffeomorph.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {E' : Type u…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Diffeomorph.image_eq_preimage_symm`：image_eq_preimage_symm (h : M ≃ₘ^n⟮I
, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem contMDiffWithinAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s x}
    (hm : m ≤ n) :
    CMDiffAt[s] m (f ∘ h) x ↔ CMDiffAt[h.symm ⁻¹' s] m f (h x) := by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [Function.comp_def, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.contMDiffWithinAt.of_le hm) (mapsTo_preimage _ _)
  · rw [← h.image_eq_preimage_symm]
    exact fun hf => hf.comp x (h.contMDiffWithinAt.of_le hm) (mapsTo_image _ _)

@[simp]
/-
**Diffeomorph.contMDiffOn_comp_diffeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeo
morph`。
形式化陈述：contMDiffOn_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s
} (hm : m <= n) : CMDiff[s] m (f ∘ h) ↔ CMDiff[h.symm ⁻¹' s] m f
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Diffeomorph.symm_apply_apply`：symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x :
 M) : h.symm (h x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contMDiffOn_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {s} (hm : m ≤ n) :
    CMDiff[s] m (f ∘ h) ↔ CMDiff[h.symm ⁻¹' s] m f :=
  h.toEquiv.forall_congr fun {_} => by
    simp only [hm, coe_toEquiv, h.symm_apply_apply, contMDiffWithinAt_comp_diffeomorph_iff,
      mem_preimage]

@[simp]
/-
**Diffeomorph.contMDiffAt_comp_diffeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeo
morph`。
形式化陈述：contMDiffAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {x
} (hm : m <= n) : CMDiffAt m (f ∘ h) x ↔ CMDiffAt m f (h x)
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiffWithinAt_comp_diffeomorph_iff`：contMDiffWithinAt_co
mp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s x} (hm : m <= n) : 
CMDiffAt[s] m (f ∘ h) x ↔ CMDiffAt[h.sym…
-/
theorem contMDiffAt_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {x} (hm : m ≤ n) :
    CMDiffAt m (f ∘ h) x ↔ CMDiffAt m f (h x) :=
  h.contMDiffWithinAt_comp_diffeomorph_iff hm

@[simp]
/-
**Diffeomorph.contMDiff_comp_diffeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomo
rph`。
形式化陈述：contMDiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} (hm 
: m <= n) : CMDiff m (f ∘ h) ↔ CMDiff m f
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `Diffeomorph.contMDiffAt_comp_diffeomorph_iff`：contMDiffAt_comp_diffeomor
ph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {x} (hm : m <= n) : CMDiffAt m (f 
∘ h) x ↔ CMDiffAt m f (h x)
-/
theorem contMDiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} (hm : m ≤ n) :
    CMDiff m (f ∘ h) ↔ CMDiff m f :=
  h.toEquiv.forall_congr fun _ ↦ h.contMDiffAt_comp_diffeomorph_iff hm

@[simp]
/-
**Diffeomorph.contMDiffWithinAt_diffeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Diffeomorph`。
形式化陈述：contMDiffWithinAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' ->
 M} (hm : m <= n) {s x} : CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m f x
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Diffeomorph.symm_apply_apply`：symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x :
 M) : h.symm (h x) = x
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContMDiffAt.of_le`：ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le :
 m <= n) : ContMDiffAt I I' m f x
· 使用定理 `Diffeomorph.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {E' : Type u…
-/
theorem contMDiffWithinAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n)
    {s x} : CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m f x :=
  ⟨fun Hhf => by
    simpa only [Function.comp_def, h.symm_apply_apply] using
      (h.symm.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hhf,
    fun Hf => (h.contMDiffAt.of_le hm).comp_contMDiffWithinAt _ Hf⟩

@[simp]
/-
**Diffeomorph.contMDiffAt_diffeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeo
morph`。
形式化陈述：contMDiffAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (h
m : m <= n) {x} : CMDiffAt m (h ∘ f) x ↔ CMDiffAt m f x
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiffWithinAt_diffeomorph_comp_iff`：contMDiffWithinAt_di
ffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s x} : 
CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m …
-/
theorem contMDiffAt_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {x} :
    CMDiffAt m (h ∘ f) x ↔ CMDiffAt m f x :=
  h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
/-
**Diffeomorph.contMDiffOn_diffeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeo
morph`。
形式化陈述：contMDiffOn_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (h
m : m <= n) {s} : CMDiff[s] m (h ∘ f) ↔ CMDiff[s] m f
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Diffeomorph.contMDiffWithinAt_diffeomorph_comp_iff`：contMDiffWithinAt_di
ffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s x} : 
CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m …
-/
theorem contMDiffOn_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) {s} :
    CMDiff[s] m (h ∘ f) ↔ CMDiff[s] m f :=
  forall₂_congr fun _ _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm

@[simp]
/-
**Diffeomorph.contMDiff_diffeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomo
rph`。
形式化陈述：contMDiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm 
: m <= n) : CMDiff m (h ∘ f) ↔ CMDiff m f
参数：h : M ≃ₘ^n⟮I, J⟯ N；hm : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Diffeomorph.contMDiffWithinAt_diffeomorph_comp_iff`：contMDiffWithinAt_di
ffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s x} : 
CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m …
-/
theorem contMDiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M} (hm : m ≤ n) :
    CMDiff m (h ∘ f) ↔ CMDiff m f :=
  forall_congr' fun _ => h.contMDiffWithinAt_diffeomorph_comp_iff hm
/-
**Diffeomorph.toOpenPartialHomeomorph_mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 
`Diffeomorph`。
形式化陈述：toOpenPartialHomeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0)
 : h.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable I J
参数：h : M ≃ₘ^n⟮I, J⟯ N；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.mdifferentiableOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {E' : Type u…
-/
theorem toOpenPartialHomeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    h.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable I J :=
  ⟨h.mdifferentiableOn _ hn, h.symm.mdifferentiableOn _ hn⟩
/-
**Diffeomorph.uniqueMDiffOn_image_aux** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：uniqueMDiffOn_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set M} (hs
 : UniqueMDiff[s]) : UniqueMDiff[h '' s]
参数：h : M ≃ₘ^n⟮I, J⟯ N；hn : n != 0；hs : UniqueMDiff[s]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Diffeomorph.image_eq_preimage_symm`：image_eq_preimage_symm (h : M ≃ₘ^n⟮I
, J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_target`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   e.t
oOpenPartialHomeomorph.target =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_symm_apply`：∀ {X : Type u_1} {Y : Typ
e u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),  
 ↑e.toOpenPartialHomeomorph.symm = …
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniqueMDiffOn.uniqueMDiffOn_preimage`：UniqueMDiffOn.uniqueMDiffOn_preima
ge (hs : UniqueMDiff[s]) {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiabl
e I I') : UniqueMDiff[e.ta…
· 使用定理 `Diffeomorph.toOpenPartialHomeomorph_mdifferentiable`：toOpenPartialHomeom
orph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) : h.toHomeomorph.toOpenP
artialHomeomorph.MDifferentiable I J
-/
theorem uniqueMDiffOn_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {s : Set M}
    (hs : UniqueMDiff[s]) : UniqueMDiff[h '' s] := by
  convert! hs.uniqueMDiffOn_preimage (h.toOpenPartialHomeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage_symm]

@[simp]
/-
**Diffeomorph.uniqueMDiffOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set M} : Uniqu
eMDiff[h '' s] ↔ UniqueMDiff[s]
参数：h : M ≃ₘ^n⟮I, J⟯ N；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.uniqueMDiffOn_image_aux`：uniqueMDiffOn_image_aux (h : M ≃ₘ^n
⟮I, J⟯ N) (hn : n != 0) {s : Set M} (hs : UniqueMDiff[s]) : UniqueMDiff[h '' s]
· 使用定理 `Diffeomorph.symm_image_image`：symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s :
 Set M) : h.symm '' h '' s = s
-/
theorem uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {s : Set M} :
    UniqueMDiff[h '' s] ↔ UniqueMDiff[s] :=
  ⟨fun hs => h.symm_image_image s ▸ h.symm.uniqueMDiffOn_image_aux hn hs,
    h.uniqueMDiffOn_image_aux hn⟩

@[simp]
/-
**Diffeomorph.uniqueMDiffOn_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：uniqueMDiffOn_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n != 0) {s : Set N} : Un
iqueMDiff[h ⁻¹' s] ↔ UniqueMDiff[s]
参数：h : M ≃ₘ^n⟮I, J⟯ N；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.uniqueMDiffOn_image`：uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N
) (hn : n != 0) {s : Set M} : UniqueMDiff[h '' s] ↔ UniqueMDiff[s]
· 使用定理 `Diffeomorph.symm_image_eq_preimage`：symm_image_eq_preimage (h : M ≃ₘ^n⟮I
, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s
-/
theorem uniqueMDiffOn_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {s : Set N} :
    UniqueMDiff[h ⁻¹' s] ↔ UniqueMDiff[s] :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueMDiffOn_image hn

@[simp]
/-
**Diffeomorph.uniqueDiffOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：uniqueDiffOn_image (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : Set
 E} : UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s
参数：h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Diffeomorph.uniqueMDiffOn_image`：uniqueMDiffOn_image (h : M ≃ₘ^n⟮I, J⟯ N
) (hn : n != 0) {s : Set M} : UniqueMDiff[h '' s] ↔ UniqueMDiff[s]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniqueDiffOn_image (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n ≠ 0) {s : Set E} :
    UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s := by
  simp only [← uniqueMDiffOn_iff_uniqueDiffOn, uniqueMDiffOn_image _ hn]

@[simp]
/-
**Diffeomorph.uniqueDiffOn_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：uniqueDiffOn_preimage (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : 
Set F} : UniqueDiffOn 𝕜 (h ⁻¹' s) ↔ UniqueDiffOn 𝕜 s
参数：h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.uniqueDiffOn_image`：uniqueDiffOn_image (h : E ≃ₘ^n⟮𝓘(𝕜, E), 
𝓘(𝕜, F)⟯ F) (hn : n != 0) {s : Set E} : UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜
 s
· 使用定理 `Diffeomorph.symm_image_eq_preimage`：symm_image_eq_preimage (h : M ≃ₘ^n⟮I
, J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s
-/
theorem uniqueDiffOn_preimage (h : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (hn : n ≠ 0) {s : Set F} :
    UniqueDiffOn 𝕜 (h ⁻¹' s) ↔ UniqueDiffOn 𝕜 s :=
  h.symm_image_eq_preimage s ▸ h.symm.uniqueDiffOn_image hn

end Diffeomorph

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] E')

/-- A continuous linear equivalence between normed spaces is a diffeomorphism. -/
/-
**ContinuousLinearEquiv.toDiffeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：toDiffeomorph : E ≃ₘ[𝕜] E' where contMDiff_toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence between normed spaces is a diffeomorphism.
-/
def toDiffeomorph : E ≃ₘ[𝕜] E' where
  contMDiff_toFun := e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]
/-
**ContinuousLinearEquiv.coe_toDiffeomorph** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：coe_toDiffeomorph : ⇑e.toDiffeomorph = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toDiffeomorph : ⇑e.toDiffeomorph = e :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.symm_toDiffeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：symm_toDiffeomorph : e.symm.toDiffeomorph = e.toDiffeomorph.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toDiffeomorph : e.symm.toDiffeomorph = e.toDiffeomorph.symm :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coe_toDiffeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：coe_toDiffeomorph_symm : ⇑e.toDiffeomorph.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toDiffeomorph_symm : ⇑e.toDiffeomorph.symm = e.symm :=
  rfl

end ContinuousLinearEquiv

namespace ModelWithCorners

variable (I) (e : E ≃L[𝕜] E')

/-- Apply a continuous linear equivalence to the model vector space. -/
/-
**ModelWithCorners.transContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModelWi
thCorners`。
形式化陈述：transContinuousLinearEquiv : ModelWithCorners 𝕜 E' H where toPartialEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a continuous linear equivalence to the model vector space.
-/
def transContinuousLinearEquiv : ModelWithCorners 𝕜 E' H where
  toPartialEquiv := I.toPartialEquiv.trans e.toEquiv.toPartialEquiv
  source_eq := by simp
  convex_range' := by
    split_ifs with h
    · simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe]
      rw [range_comp]
      let := h.rclike
      let := NormedSpace.restrictScalars ℝ 𝕜 E
      let := NormedSpace.restrictScalars ℝ 𝕜 E'
      let eR : E →L[ℝ] E' := ContinuousLinearMap.restrictScalars ℝ (e : E →L[𝕜] E')
      change Convex ℝ (⇑eR '' range ↑I)
      apply I.convex_range.linear_image
    · simp [range_eq_univ_of_not_isRCLikeNormedField I h, range_comp]
  nonempty_interior' := by
    simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, toPartialEquiv_coe, range_comp,
      ContinuousLinearEquiv.image_eq_preimage_symm]
    apply Nonempty.mono (preimage_interior_subset_interior_preimage e.symm.continuous)
    rw [← ContinuousLinearEquiv.image_eq_preimage_symm]
    simpa using I.nonempty_interior
  continuous_toFun := e.continuous.comp I.continuous
  continuous_invFun := I.continuous_symm.comp e.symm.continuous

@[simp, mfld_simps]
/-
**ModelWithCorners.coe_transContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Mod
elWithCorners`。
形式化陈述：coe_transContinuousLinearEquiv : ⇑(I.transContinuousLinearEquiv e) = e ∘ I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_transContinuousLinearEquiv : ⇑(I.transContinuousLinearEquiv e) = e ∘ I :=
  rfl

@[simp, mfld_simps]
/-
**ModelWithCorners.coe_transContinuousLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间
 `ModelWithCorners`。
形式化陈述：coe_transContinuousLinearEquiv_symm : ⇑(I.transContinuousLinearEquiv e).sy
mm = I.symm ∘ e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_transContinuousLinearEquiv_symm :
    ⇑(I.transContinuousLinearEquiv e).symm = I.symm ∘ e.symm := rfl
/-
**ModelWithCorners.transContinuousLinearEquiv_range** 是 Mathlib 中的一个定理，位于命名空间 `M
odelWithCorners`。
形式化陈述：transContinuousLinearEquiv_range : range (I.transContinuousLinearEquiv e) 
= e '' range I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem transContinuousLinearEquiv_range : range (I.transContinuousLinearEquiv e) = e '' range I :=
  range_comp e I
/-
**ModelWithCorners.coe_extChartAt_transContinuousLinearEquiv** 是 Mathlib 中的一个定理，
位于命名空间 `ModelWithCorners`。
形式化陈述：coe_extChartAt_transContinuousLinearEquiv (x : M) : ⇑(extChartAt (I.transC
ontinuousLinearEquiv e) x) = e ∘ extChartAt I x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_extChartAt_transContinuousLinearEquiv (x : M) :
    ⇑(extChartAt (I.transContinuousLinearEquiv e) x) = e ∘ extChartAt I x :=
  rfl
/-
**ModelWithCorners.coe_extChartAt_transContinuousLinearEquiv_symm** 是 Mathlib 中的
一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：coe_extChartAt_transContinuousLinearEquiv_symm (x : M) : ⇑(extChartAt (I.t
ransContinuousLinearEquiv e) x).symm = (extChartAt I x).symm ∘ e.symm
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_extChartAt_transContinuousLinearEquiv_symm (x : M) :
    ⇑(extChartAt (I.transContinuousLinearEquiv e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl
/-
**ModelWithCorners.extChartAt_transContinuousLinearEquiv_target** 是 Mathlib 中的一个
定理，位于命名空间 `ModelWithCorners`。
形式化陈述：extChartAt_transContinuousLinearEquiv_target (x : M) : (extChartAt (I.tran
sContinuousLinearEquiv e) x).target = e.symm ⁻¹' (extChartAt I x).target
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `ContinuousLinearEquiv.image_eq_preimage_symm`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extChartAt_transContinuousLinearEquiv_target (x : M) :
    (extChartAt (I.transContinuousLinearEquiv e) x).target
      = e.symm ⁻¹' (extChartAt I x).target := by
  simp only [range_comp, preimage_preimage, ContinuousLinearEquiv.image_eq_preimage_symm,
    mfld_simps, ← comp_def]

end ModelWithCorners

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] F)

/-
**ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv** 是 Mathlib 中的一
个实例，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：instIsManifoldtransContinuousLinearEquiv [IsManifold I n M] : IsManifold (
I.transContinuousLinearEquiv e) n M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isManifold_of_contDiffOn`：isManifold_of_contDiffOn {𝕜 : Type*} [Nontrivi
allyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Typ
e*} [Topologic…
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `Equiv.toPartialEquiv_symm_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α 
≃ β), ↑e.toPartialEquiv.symm = ⇑e.symm
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `ContinuousLinearEquiv.image_eq_preimage_symm`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
-/
instance instIsManifoldtransContinuousLinearEquiv [IsManifold I n M] :
    IsManifold (I.transContinuousLinearEquiv e) n M := by
  refine isManifold_of_contDiffOn (I.transContinuousLinearEquiv e) n M fun e₁ e₂ h₁ h₂ => ?_
  refine e.contDiff.comp_contDiffOn
      (((contDiffGroupoid n I).compatible h₁ h₂).1.comp e.symm.contDiff.contDiffOn ?_)
  simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
    ContinuousLinearEquiv.image_eq_preimage_symm]

variable (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
/-
**ContinuousLinearEquiv.toTransContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：toTransContinuousLinearEquiv (e : E ≃L[𝕜] F) : M ≃ₘ^n⟮I, I.transContinuous
LinearEquiv e⟯ M where toEquiv
参数：e : E ≃L[𝕜] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity diffeomorphism between a manifold with model `I` and the same manif
old
with model `I.trans_diffeomorph e`.
-/
def toTransContinuousLinearEquiv (e : E ≃L[𝕜] F) : M ≃ₘ^n⟮I, I.transContinuousLinearEquiv e⟯ M where
  toEquiv := Equiv.refl M
  contMDiff_toFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) ?_
    · simp only [Equiv.coe_refl, id, (· ∘ ·), I.coe_extChartAt_transContinuousLinearEquiv,
        (extChartAt I x).right_inv hy.1]
    · exact
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial, by simp only [mfld_simps]⟩
  contMDiff_invFun x := by
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [mem_inter_iff, I.extChartAt_transContinuousLinearEquiv_target] at hy
      simp only [Equiv.coe_refl, Equiv.refl_symm, id, (· ∘ ·),
        I.coe_extChartAt_transContinuousLinearEquiv_symm, (extChartAt I x).right_inv hy.1]
    exact ⟨(extChartAt _ x).map_source (mem_extChartAt_source x), trivial, by
      simp only [e.symm_apply_apply, Equiv.refl_symm, Equiv.coe_refl, mfld_simps]⟩

variable {I M}

@[simp]
/-
**ContinuousLinearEquiv.contMDiffWithinAt_transContinuousLinearEquiv_right** 是 M
athlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiffWithinAt_transContinuousLinearEquiv_right {f : M' -> M} {x s} : C
ontMDiffWithinAt I' (I.transContinuousLinearEquiv e) n f s x ↔ CMDiffAt[s] n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiffWithinAt_diffeomorph_comp_iff`：contMDiffWithinAt_di
ffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s x} : 
CMDiffAt[s] m (h ∘ f) x ↔ CMDiffAt[s] m …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffWithinAt_transContinuousLinearEquiv_right {f : M' → M} {x s} :
    ContMDiffWithinAt I' (I.transContinuousLinearEquiv e) n f s x
      ↔ CMDiffAt[s] n f x :=
  (toTransContinuousLinearEquiv I M e).contMDiffWithinAt_diffeomorph_comp_iff le_rfl

@[simp]
/-
**ContinuousLinearEquiv.contMDiffAt_transContinuousLinearEquiv_right** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiffAt_transContinuousLinearEquiv_right {f : M' -> M} {x} : ContMDiff
At I' (I.transContinuousLinearEquiv e) n f x ↔ CMDiffAt n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiffAt_diffeomorph_comp_iff`：contMDiffAt_diffeomorph_co
mp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {x} : CMDiffAt m (h 
∘ f) x ↔ CMDiffAt m f x
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffAt_transContinuousLinearEquiv_right {f : M' → M} {x} :
    ContMDiffAt I' (I.transContinuousLinearEquiv e) n f x ↔ CMDiffAt n f x :=
  (toTransContinuousLinearEquiv I M e).contMDiffAt_diffeomorph_comp_iff le_rfl

@[simp]
/-
**ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiffOn_transContinuousLinearEquiv_right {f : M' -> M} {s} : ContMDiff
On I' (I.transContinuousLinearEquiv e) n f s ↔ CMDiff[s] n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiffOn_diffeomorph_comp_iff`：contMDiffOn_diffeomorph_co
mp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) {s} : CMDiff[s] m (h
 ∘ f) ↔ CMDiff[s] m f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffOn_transContinuousLinearEquiv_right {f : M' → M} {s} :
    ContMDiffOn I' (I.transContinuousLinearEquiv e) n f s ↔ CMDiff[s] n f :=
  (toTransContinuousLinearEquiv I M e).contMDiffOn_diffeomorph_comp_iff le_rfl

@[simp]
/-
**ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiff_transContinuousLinearEquiv_right {f : M' -> M} : ContMDiff I' (I
.transContinuousLinearEquiv e) n f ↔ CMDiff n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.contMDiff_diffeomorph_comp_iff`：contMDiff_diffeomorph_comp_i
ff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' -> M} (hm : m <= n) : CMDiff m (h ∘ f) ↔ CMD
iff m f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiff_transContinuousLinearEquiv_right {f : M' → M} :
    ContMDiff I' (I.transContinuousLinearEquiv e) n f ↔ CMDiff n f :=
  (toTransContinuousLinearEquiv I M e).contMDiff_diffeomorph_comp_iff le_rfl

@[simp]
/-
**ContinuousLinearEquiv.contMDiffWithinAt_transContinuousLinearEquiv_left** 是 Ma
thlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiffWithinAt_transContinuousLinearEquiv_left {f : M -> M'} {x s} : Co
ntMDiffWithinAt (I.transContinuousLinearEquiv e) I' n f s x ↔ CMDiffAt[s] n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Diffeomorph.contMDiffWithinAt_comp_diffeomorph_iff`：contMDiffWithinAt_co
mp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s x} (hm : m <= n) : 
CMDiffAt[s] m (f ∘ h) x ↔ CMDiffAt[h.sym…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffWithinAt_transContinuousLinearEquiv_left {f : M → M'} {x s} :
    ContMDiffWithinAt (I.transContinuousLinearEquiv e) I' n f s x ↔ CMDiffAt[s] n f x :=
  ((toTransContinuousLinearEquiv I M e).contMDiffWithinAt_comp_diffeomorph_iff le_rfl).symm

@[simp]
/-
**ContinuousLinearEquiv.contMDiffAt_transContinuousLinearEquiv_left** 是 Mathlib 
中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiffAt_transContinuousLinearEquiv_left {f : M -> M'} {x} : ContMDiffA
t (I.transContinuousLinearEquiv e) I' n f x ↔ CMDiffAt n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Diffeomorph.contMDiffAt_comp_diffeomorph_iff`：contMDiffAt_comp_diffeomor
ph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {x} (hm : m <= n) : CMDiffAt m (f 
∘ h) x ↔ CMDiffAt m f (h x)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffAt_transContinuousLinearEquiv_left {f : M → M'} {x} :
    ContMDiffAt (I.transContinuousLinearEquiv e) I' n f x ↔ CMDiffAt n f x :=
  ((toTransContinuousLinearEquiv I M e).contMDiffAt_comp_diffeomorph_iff le_rfl).symm

@[simp]
/-
**ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left** 是 Mathlib 
中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiffOn_transContinuousLinearEquiv_left {f : M -> M'} {s} : ContMDiffO
n (I.transContinuousLinearEquiv e) I' n f s ↔ CMDiff[s] n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Diffeomorph.contMDiffOn_comp_diffeomorph_iff`：contMDiffOn_comp_diffeomor
ph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} {s} (hm : m <= n) : CMDiff[s] m (f
 ∘ h) ↔ CMDiff[h.symm ⁻¹' s] m f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffOn_transContinuousLinearEquiv_left {f : M → M'} {s} :
    ContMDiffOn (I.transContinuousLinearEquiv e) I' n f s ↔ CMDiff[s] n f :=
  ((toTransContinuousLinearEquiv I M e).contMDiffOn_comp_diffeomorph_iff le_rfl).symm

@[simp]
/-
**ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：contMDiff_transContinuousLinearEquiv_left {f : M -> M'} : ContMDiff (I.tra
nsContinuousLinearEquiv e) I' n f ↔ CMDiff n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Diffeomorph.contMDiff_comp_diffeomorph_iff`：contMDiff_comp_diffeomorph_i
ff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N -> M'} (hm : m <= n) : CMDiff m (f ∘ h) ↔ CMD
iff m f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiff_transContinuousLinearEquiv_left {f : M → M'} :
    ContMDiff (I.transContinuousLinearEquiv e) I' n f ↔ CMDiff n f :=
  ((toTransContinuousLinearEquiv I M e).contMDiff_comp_diffeomorph_iff le_rfl).symm

end ContinuousLinearEquiv

namespace Diffeomorph

section Constructions

section Product

/-- Product of two diffeomorphisms. -/
/-
**Diffeomorph.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') : (M × N) ≃ₘ^n⟮I
.prod J, I'.prod J'⟯ M' × N' where contMDiff_toFun
参数：h₁ : M ≃ₘ^n⟮I, I'⟯ M'；h₂ : N ≃ₘ^n⟮J, J'⟯ N'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two diffeomorphisms.
-/
def prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ M' × N' where
  contMDiff_toFun := (h₁.contMDiff.comp contMDiff_fst).prodMk (h₂.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (h₁.symm.contMDiff.comp contMDiff_fst).prodMk (h₂.symm.contMDiff.comp contMDiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
/-
**Diffeomorph.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：prodCongr_symm (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') : (h₁.prodC
ongr h₂).symm = h₁.symm.prodCongr h₂.symm
参数：h₁ : M ≃ₘ^n⟮I, I'⟯ M'；h₂ : N ≃ₘ^n⟮J, J'⟯ N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
/-
**Diffeomorph.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') : ⇑(h₁.prodC
ongr h₂) = Prod.map h₁ h₂
参数：h₁ : M ≃ₘ^n⟮I, I'⟯ M'；h₂ : N ≃ₘ^n⟮J, J'⟯ N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : N ≃ₘ^n⟮J, J'⟯ N') :
    ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (I J J' M N N' n)

/-- `M × N` is diffeomorphic to `N × M`. -/
/-
**Diffeomorph.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：prodComm : (M × N) ≃ₘ^n⟮I.prod J, J.prod I⟯ N × M where contMDiff_toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M × N` is diffeomorphic to `N × M`.
-/
def prodComm : (M × N) ≃ₘ^n⟮I.prod J, J.prod I⟯ N × M where
  contMDiff_toFun := contMDiff_snd.prodMk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prodMk contMDiff_fst
  toEquiv := Equiv.prodComm M N

@[simp]
/-
**Diffeomorph.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：prodComm_symm : (prodComm I J M N n).symm = prodComm J I N M n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_symm : (prodComm I J M N n).symm = prodComm J I N M n :=
  rfl

@[simp]
/-
**Diffeomorph.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：coe_prodComm : ⇑(prodComm I J M N n) = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm : ⇑(prodComm I J M N n) = Prod.swap :=
  rfl

/-- `(M × N) × N'` is diffeomorphic to `M × (N × N')`. -/
/-
**Diffeomorph.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：prodAssoc : ((M × N) × N') ≃ₘ^n⟮(I.prod J).prod J', I.prod (J.prod J')⟯ M 
× N × N' where contMDiff_toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(M × N) × N'` is diffeomorphic to `M × (N × N')`.
-/
def prodAssoc : ((M × N) × N') ≃ₘ^n⟮(I.prod J).prod J', I.prod (J.prod J')⟯ M × N × N' where
  contMDiff_toFun :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  toEquiv := Equiv.prodAssoc M N N'

end

end Product

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {N J : Type*} [TopologicalSpace N] [ChartedSpace H N] {J : ModelWithCorners 𝕜 E' H}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H N']

/-- The sum of two diffeomorphisms: this is `Sum.map` as a diffeomorphism. -/
/-
**Diffeomorph.sumCongr** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：sumCongr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) : Diffe
omorph I J (M oplus M') (N oplus N') n where toEquiv
参数：φ : Diffeomorph I J M N n；ψ : Diffeomorph I J M' N' n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two diffeomorphisms: this is `Sum.map` as a diffeomorphism.
-/
def sumCongr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    Diffeomorph I J (M ⊕ M') (N ⊕ N') n where
  toEquiv := Equiv.sumCongr φ.toEquiv ψ.toEquiv
  contMDiff_toFun := ContMDiff.sumMap φ.contMDiff_toFun ψ.contMDiff_toFun
  contMDiff_invFun := ContMDiff.sumMap φ.contMDiff_invFun ψ.contMDiff_invFun
/-
**Diffeomorph.sumCongr_symm_symm** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumCongr_symm_symm (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' 
n) : sumCongr φ.symm ψ.symm = (sumCongr φ ψ).symm
参数：φ : Diffeomorph I J M N n；ψ : Diffeomorph I J M' N' n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumCongr_symm_symm (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    sumCongr φ.symm ψ.symm = (sumCongr φ ψ).symm := rfl

@[simp, mfld_simps]
/-
**Diffeomorph.sumCongr_coe** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumCongr_coe (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) : s
umCongr φ ψ = Sum.map φ ψ
参数：φ : Diffeomorph I J M N n；ψ : Diffeomorph I J M' N' n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumCongr_coe (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    sumCongr φ ψ = Sum.map φ ψ := rfl
/-
**Diffeomorph.sumCongr_inl** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumCongr_inl (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) : (
sumCongr φ ψ) ∘ Sum.inl = Sum.inl ∘ φ
参数：φ : Diffeomorph I J M N n；ψ : Diffeomorph I J M' N' n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumCongr_inl (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    (sumCongr φ ψ) ∘ Sum.inl = Sum.inl ∘ φ := rfl
/-
**Diffeomorph.sumCongr_inr** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumCongr_inr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) : (
sumCongr φ ψ) ∘ Sum.inr = Sum.inr ∘ ψ
参数：φ : Diffeomorph I J M N n；ψ : Diffeomorph I J M' N' n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumCongr_inr (φ : Diffeomorph I J M N n) (ψ : Diffeomorph I J M' N' n) :
    (sumCongr φ ψ) ∘ Sum.inr = Sum.inr ∘ ψ := rfl

variable (I M M' n) in
/-- The canonical diffeomorphism `M ⊕ M' → M' ⊕ M`: this is `Sum.swap` as a diffeomorphism -/
/-
**Diffeomorph.sumComm** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：sumComm : Diffeomorph I I (M oplus M') (M' oplus M) n where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiff.swap`：ContMDiff.swap : ContMDiff I I n (@Sum.swap M M')

--- 原说明 ---
The canonical diffeomorphism `M ⊕ M' → M' ⊕ M`: this is `Sum.swap` as a diffeomo
rphism
-/
def sumComm : Diffeomorph I I (M ⊕ M') (M' ⊕ M) n where
  toEquiv := Equiv.sumComm M M'
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

@[simp, mfld_simps]
/-
**Diffeomorph.sumComm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：sumComm_coe : (Diffeomorph.sumComm I M n M' : (M oplus M') -> (M' oplus M)
) = Sum.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumComm_coe : (Diffeomorph.sumComm I M n M' : (M ⊕ M') → (M' ⊕ M)) = Sum.swap := rfl

@[simp, mfld_simps]
/-
**Diffeomorph.sumComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：sumComm_symm : (Diffeomorph.sumComm I M n M').symm = Diffeomorph.sumComm I
 M' n M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumComm_symm : (Diffeomorph.sumComm I M n M').symm = Diffeomorph.sumComm I M' n M := rfl

variable (I M M' n) in
/-
**Diffeomorph.sumComm_inl** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumComm_inl : (Diffeomorph.sumComm I M n M') ∘ Sum.inl = Sum.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.swap_inl`：∀ {α : Type u_1} {β : Type u_2} {x : α}, (Sum.inl x).swap 
= Sum.inr x
-/
lemma sumComm_inl : (Diffeomorph.sumComm I M n M') ∘ Sum.inl = Sum.inr := by
  ext
  exact Sum.swap_inl

variable (I M M' n) in
/-
**Diffeomorph.sumComm_inr** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumComm_inr : (Diffeomorph.sumComm I M n M') ∘ Sum.inr = Sum.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.swap_inr`：∀ {α : Type u_1} {β : Type u_2} {x : β}, (Sum.inr x).swap 
= Sum.inl x
-/
lemma sumComm_inr : (Diffeomorph.sumComm I M n M') ∘ Sum.inr = Sum.inl := by
  ext
  exact Sum.swap_inr

variable (I M M' M'' n) in
/-- The canonical diffeomorphism `(M ⊕ N) ⊕ P → M ⊕ (N ⊕ P)` -/
/-
**Diffeomorph.sumAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：sumAssoc : Diffeomorph I I ((M oplus M') oplus M'') (M oplus (M' oplus M''
)) n where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical diffeomorphism `(M ⊕ N) ⊕ P → M ⊕ (N ⊕ P)`
-/
def sumAssoc : Diffeomorph I I ((M ⊕ M') ⊕ M'') (M ⊕ (M' ⊕ M'')) n where
  toEquiv := Equiv.sumAssoc M M' M''
  contMDiff_toFun := by
    apply ContMDiff.sumElim
    · exact contMDiff_id.sumMap ContMDiff.inl
    · exact ContMDiff.inr.comp ContMDiff.inr
  contMDiff_invFun := by
    apply ContMDiff.sumElim
    · exact ContMDiff.inl.comp ContMDiff.inl
    · exact ContMDiff.inr.sumMap contMDiff_id

@[simp]
/-
**Diffeomorph.sumAssoc_coe** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：sumAssoc_coe : (sumAssoc I M n M' M'' : (M oplus M') oplus M'' -> M oplus 
(M' oplus M'')) = Equiv.sumAssoc M M' M''
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_coe :
    (sumAssoc I M n M' M'' : (M ⊕ M') ⊕ M'' → M ⊕ (M' ⊕ M'')) = Equiv.sumAssoc M M' M'' := rfl

variable (I M n) in
/-- The canonical diffeomorphism `M ⊕ ∅ → M` -/
/-
**Diffeomorph.sumEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：sumEmpty [IsEmpty M'] : Diffeomorph I I (M oplus M') M n where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiff.inl`：ContMDiff.inl : ContMDiff I I n (@Sum.inl M M')

--- 原说明 ---
The canonical diffeomorphism `M ⊕ ∅ → M`
-/
def sumEmpty [IsEmpty M'] : Diffeomorph I I (M ⊕ M') M n where
  toEquiv := Equiv.sumEmpty M M'
  contMDiff_toFun := contMDiff_id.sumElim fun x ↦ (IsEmpty.false x).elim
  contMDiff_invFun := ContMDiff.inl

@[simp, mfld_simps]
/-
**Diffeomorph.sumEmpty_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Diffeomorph`。
形式化陈述：sumEmpty_toEquiv [IsEmpty M'] : (sumEmpty I M n).toEquiv = Equiv.sumEmpty 
M M'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumEmpty_toEquiv [IsEmpty M'] : (sumEmpty I M n).toEquiv = Equiv.sumEmpty M M' := rfl

@[simp, mfld_simps]
/-
**Diffeomorph.sumEmpty_apply_inl** 是 Mathlib 中的一个引理，位于命名空间 `Diffeomorph`。
形式化陈述：sumEmpty_apply_inl [IsEmpty M'] (x : M) : (sumEmpty I M (M'
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumEmpty_apply_inl [IsEmpty M'] (x : M) : (sumEmpty I M (M' := M') n) (Sum.inl x) = x := rfl

/-- The unique diffeomorphism between two empty types -/
/-
**Diffeomorph.empty** 是 Mathlib 中的一个定义，位于命名空间 `Diffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_5} →             [inst_3 : TopologicalSpace H] →          
     {I : ModelWithCorners 𝕜 E H} →                 {M : Type u_9} →            
       [inst_4 : TopologicalSpace M] →                     [inst_5 : ChartedSpac
e H M] →                       {n : WithTop ℕ∞} →                         {M' : 
Type u_13} →                           [inst_6 : TopologicalSpace M'] →         
                    [inst_7 : ChartedSpace H M'] → [IsEmpty M] → [IsEmpty M'] → 
Diffeomorph I I M M' n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique diffeomorphism between two empty types
-/
protected def empty [IsEmpty M] [IsEmpty M'] : Diffeomorph I I M M' n where
  __ := Equiv.equivOfIsEmpty M M'
  contMDiff_toFun x := (IsEmpty.false x).elim
  contMDiff_invFun x := (IsEmpty.false x).elim

end disjointUnion

end Constructions

end Diffeomorph

