/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Anatole Dedecker, Yongxi Lin, Patrick Massot, Oliver Nash, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite

/-!
# Fredholm operators between topological vector spaces

Fix `𝕜` a complete `NontriviallyNormedField`, and let `E`, `F` be two Hausdorff topological vector
spaces over `𝕜`.

We say that a continuous linear map `T : E →L[𝕜] F` is a **Fredholm operator** if it satisfies
the following four equivalent conditions:

1. `T` is strict, its range is closed and has finite codimension, and its kernel is (topologically)
  complemented and has finite dimension. This is chosen as the definition, see `IsFredholm`.
2. `T` admits a continuous **quasi-inverse**, in the sense of `LinearMap.IsQuasiInverse`.
3. There are closed finite-codimension subspaces `E₁` and `F₁` of `E` and `F` between which `T`
  induces an isomorphism.
4. `T` admits a `FredholmPackage`: there are topological decompositions `E = E₁ ⊕ E₀`,
  `F = F₁ ⊕ F₀`, where `E₀` and `F₀` are finite dimensional, and an isomorphism `Φ : E₁ ≃L[𝕜] F₁`
  such that `T` is zero on `E₀` and coincides with `Φ` on `E₁`; in other words, in these
  decompositions, `T` is given by the matrix $\begin{pmatrix} Φ & 0 \cr 0 & 0 \end{pmatrix}$.

## Main definitions

* `ContinuousLinearMap.IsFredholm`: a continuous linear map `u : E →L[𝕜] F` is a
  **Fredholm operator** if it is strict, its range is closed and has finite codimension, and its
  kernel is (topologically) complemented and has finite dimension.
* `FredholmDecomposition`: a **Fredholm decomposition** of a topological vector space `E` is the
  data of two subspaces `X₀` and `X₁` which are topological complements, and where `X₀` is finite
  dimensional.
* `ContinuousLinearMap.FredholmPackage`: a **Fredholm package** for `u : E →L[𝕜] F` is the data of
  Fredholm decompositions `decDom` and `decCodom` of `E` and `F` respectively, together with
  a continuous linear equivalence `equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁` between the "essential"
  (i.e. finite codimension) parts of these decompositions, such that `u` equals the composition
  `decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj`.

Note that the data of a `FredholmPackage` for an operator is morally the strongest of the
equivalent ways to assume that `u` is Fredholm (for example, it is clear how to build a canonical
continuous quasi-inverse of `u` from such a package).

Hence, you should not typically prove that an operator is Fredholm by building a Fredholm package
(consider using `IsFredholm.of_isInvertible_restrict`); instead, when you know that an operator is
Fredholm, you can obtain a `FredholmPackage` from `IsFredholm.nonempty_fredholmPackage`
in order to conveniently use the full strength of Fredholmness.

## Main statements

### Equivalent criteria

* `ContinuousLinearMap.isFredholm_tfae`: the equivalence between conditions 1, 2, 3 and 4 above.
  In practice, most of the interesting directions should be covered by specific API lemmas.
* `ContinuousLinearMap.FredholmPackage.isQuasiInverse`: given a `FredholmPackage` for `u`,
  one can build a canonical continuous quasi-inverse of `u`.
* `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict`: if a continuous linear map induces
  an isomorphism between finite codimension subspaces, then it is Fredholm.
* `ContinuousLinearMap.IsFredholm.of_restrict` (not in Mathlib yet) is a generalization
  of the above: if a continuous linear map induces a Fredholm operator between finite codimension
  subspaces, then the original map is Fredholm as well.
* `IsFredholm.nonempty_fredholmPackage`: every Fredholm operator admits a Fredholm package.
  This is the primary way to obtain Fredholm packages.

## Implementation details

We largely follow [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023],
in particular for the proof of equivalence of the four conditions above.
Here are some notable changes:

* Bourbaki restricts itself to locally convex spaces over `ℝ` or `ℂ`. Yet, under close inspection,
  this assumption plays very little role in the beginning of the theory. In fact, at the very mild
  cost of assuming that the kernel is complemented in the definition of `IsFredholm` (which follows
  from the finiteness assumption if Hahn-Banach is available), we generalize the beginning of the
  theory to topological vector spaces over any complete nontrivially normed field. In particular,
  our theory naturally captures p-adic Fredholm operators.
* Bourbaki chooses the existence of a continuous quasi-inverse as the definition of being Fredholm.
  Our choice differs for a very practical reason: it is much simpler to spell out formally
  "`u` has a continuous quasi-inverse" than "`u` is strict, its range is closed and has finite
  codimension, and its kernel is complemented and has finite dimension". Hence we prefer to give
  a name to the latter.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023]
-/

@[expose] public noncomputable section

open Topology Submodule LinearMap
open Set (MapsTo)
open LinearMap.FiniteRangeSetoid

namespace ContinuousLinearMap
section TVS

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [TopologicalSpace E] [TopologicalSpace F]

/-!
## Definition and equivalent conditions
-/

section DefTFAE

section IsFredholm

/-- A continuous linear map `u : E →L[𝕜] F` is a **Fredholm operator** if it is strict,
its range is closed and has finite codimension, and its kernel is (topologically) complemented and
has finite dimension.

See also `isFredholm_tfae` for other equivalent characterizations.
We will also prove later (not in Mathlib yet) that for maps between Banach (or even Fréchet)
spaces over `ℝ` or `ℂ`, all the conditions follow from the kernel and cokernel having finite
dimension. -/
/-
**ContinuousLinearMap.IsFredholm** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : AddCommGroup E] →           [inst_2 
: AddCommGroup F] →             [inst_3 : _root_.Module 𝕜 E] →               [in
st_4 : _root_.Module 𝕜 F] →                 [inst_5 : TopologicalSpace E] → [ins
t_6 : TopologicalSpace F] → (E →L[𝕜] F) → Prop
参数：E →L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear map `u : E →L[𝕜] F` is a **Fredholm operator** if it is stri
ct,
its range is closed and has finite codimension, and its kernel is (topologically
) complemented and
has finite dimension.

See also `isFredholm_tfae` for other equivalent characterizations.
We will also prove later (not in Mathlib yet) that for maps between Banach (or e
ven Fréchet)
spaces over `ℝ` or `ℂ`, all the conditions follow from the kernel and cokernel h
aving finite
dimension.
-/
structure IsFredholm (u : E →L[𝕜] F) : Prop where
  isStrictMap : IsStrictMap u
  isClosed_range : IsClosed (u.range : Set F)
  finite_ker : FiniteDimensional 𝕜 u.ker
  finite_coker : u.range.CoFG
  closedComplemented_ker : u.ker.ClosedComplemented

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/-- A Fredholm operator has (topologically) complemented range. -/
/-
**ContinuousLinearMap.IsFredholm.closedComplemented_range** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap.IsFredholm`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] [CompleteSpace 𝕜] [IsTopologicalAddGroup F] [ContinuousSMu
l 𝕜 F] {u : E →L[𝕜] F},   u.IsFredholm → (↑u).range.ClosedComplemented
参数：↑u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsFredholm.finite_coker`：∀ {𝕜 : Type u_1} {E : Type 
u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]
   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `Submodule.ClosedComplemented.of_finiteDimensional_quotient`：Submodule.Cl
osedComplemented.of_finiteDimensional_quotient {p : Submodule 𝕜 E} (hp : IsClose
d (p : Set E)) [hq : FiniteDimensional 𝕜 (E ⧸ p)…
· 使用定理 `ContinuousLinearMap.IsFredholm.isClosed_range`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup 
E]   [inst_2 : AddCommGroup F] [ins…

--- 原说明 ---
A Fredholm operator has (topologically) complemented range.
-/
lemma IsFredholm.closedComplemented_range {u : E →L[𝕜] F} (u_fred : IsFredholm u) :
    u.range.ClosedComplemented :=
  have := u_fred.finite_coker
  ClosedComplemented.of_finiteDimensional_quotient u_fred.isClosed_range

end IsFredholm

section FredholmPackage

variable (𝕜 E) in
/-- A **Fredholm decomposition** of a topological vector space `E` is the data of two subspaces
`X₀` and `X₁` which are topological complements, and where `X₀` is finite dimensional.

Note that we purposefully use the index `₀` for the "inessential" (i.e. finite dimensional)
part of the decomposition. -/
/-
**ContinuousLinearMap._root_.FredholmDecomposition** 是 Mathlib 中的一个结构，位于命名空间 `Co
ntinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **Fredholm decomposition** of a topological vector space `E` is the data of tw
o subspaces
`X₀` and `X₁` which are topological complements, and where `X₀` is finite dimens
ional.

Note that we purposefully use the index `₀` for the "inessential" (i.e. finite d
imensional)
part of the decomposition.
-/
structure _root_.FredholmDecomposition where
  /-- The inessential (i.e. finite dimensional) part of a Fredholm decomposition. -/
  X₀ : Submodule 𝕜 E
  /-- The essential (i.e. finite codimensional) part of a Fredholm decomposition. -/
  X₁ : Submodule 𝕜 E
  isTopCompl : IsTopCompl X₁ X₀
  finite_X₀ : FiniteDimensional 𝕜 X₀

/-- Given a Fredholm decomposition `dec` of the space `E`, `dec.proj` is the (continuous linear)
projection onto the "essential part" `dec.X₁` along the "inessential part" `dec.X₀`.
This is a Fredholm operator. -/
/-
**ContinuousLinearMap._root_.FredholmDecomposition.proj** 是 Mathlib 中的一个缩写定义，位于命
名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Fredholm decomposition `dec` of the space `E`, `dec.proj` is the (contin
uous linear)
projection onto the "essential part" `dec.X₁` along the "inessential part" `dec.
X₀`.
This is a Fredholm operator.
-/
abbrev _root_.FredholmDecomposition.proj (dec : FredholmDecomposition 𝕜 E) :
    E →L[𝕜] dec.X₁ := dec.X₁.projectionOntoL dec.X₀ dec.isTopCompl

/-- Let `u : E →L[𝕜] F` be a continuous linear map. A **Fredholm package** for `u` is the data of
Fredholm decompositions `decDom` and `decCodom` of `E` and `F` respectively, together with
a continuous linear equivalence `equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁` between the "essential"
(i.e. finite codimension) parts of these decompositions, such that `u` equals the composition
`decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj`. In other words, in these
"essential ⊕ inessential" decompositions, the matrix of `u` is
$\begin{pmatrix} \texttt{equiv} & 0 \cr 0 & 0 \end{pmatrix}$.

We will show in `isFredholm_tfae` that an operator is Fredholm if and only if it admits
a Fredholm package. In practice, the condition that `u` is Fredholm (`IsFredholm`) is always easier
to prove, so if you need a Fredholm package you should probably get it from
`IsFredholm.nonempty_fredholmPackage` or `IsFredholm.fredholmPackage`. -/
/-
**ContinuousLinearMap.FredholmPackage** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : AddCommGroup E] →           [inst_2 
: AddCommGroup F] →             [inst_3 : _root_.Module 𝕜 E] →               [in
st_4 : _root_.Module 𝕜 F] →                 [inst_5 : TopologicalSpace E] → [ins
t_6 : TopologicalSpace F] → (E →L[𝕜] F) → Type (max u_2 u_3)
参数：E →L[𝕜] F；max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `u : E →L[𝕜] F` be a continuous linear map. A **Fredholm package** for `u` i
s the data of
Fredholm decompositions `decDom` and `decCodom` of `E` and `F` respectively, tog
ether with
a continuous linear equivalence `equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁` between th
e "essential"
(i.e. finite codimension) parts of these decompositions, such that `u` equals th
e composition
`decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj`. In other words, in these
"essential ⊕ inessential" decompositions, the matrix of `u` is
$\begin{pmatrix} \texttt{equiv} & 0 \cr 0 & 0 \end{pmatrix}$.

We will show in `isFredholm_tfae` that an operator is Fredholm if and only if it
 admits
a Fredholm package. In practice, the condition that `u` is Fredholm (`IsFredholm
`) is always easier
to prove, so if you need a Fredholm package you should probably get it from
`IsFredholm.nonempty_fredholmPackage` or `IsFredholm.fredholmPackage`.
-/
structure FredholmPackage (u : E →L[𝕜] F) where
  /-- A `FredholmDecomposition` of the domain. -/
  decDom : FredholmDecomposition 𝕜 E
  /-- A `FredholmDecomposition` of the codomain. -/
  decCodom : FredholmDecomposition 𝕜 F
  /-- An isomorphism between the essential parts of `decDom` and `decCodom`. -/
  equiv : decDom.X₁ ≃L[𝕜] decCodom.X₁
  eq_equiv : u = decCodom.X₁.subtypeL ∘L equiv ∘L decDom.proj
/-
**ContinuousLinearMap.FredholmPackage.ker_eq** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] {u : E →L[𝕜] F} (pkg : u.FredholmPackage), (↑u).ker = pkg.
decDom.X₀
参数：pkg : u.FredholmPackage；↑u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `FredholmDecomposition.isTopCompl`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module
 𝕜 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.FredholmPackage.eq_equiv`：∀ {𝕜 : Type u_1} {E : Type
 u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E
]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `Submodule.ker_projectionOnto`：ker_projectionOnto (h : IsCompl p q) : ker
 (projectionOnto p q h) = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma FredholmPackage.ker_eq {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    u.ker = pkg.decDom.X₀ := by simp [pkg.eq_equiv, ker_comp]
/-
**ContinuousLinearMap.FredholmPackage.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] {u : E →L[𝕜] F} (pkg : u.FredholmPackage), (↑u).range = pk
g.decCodom.X₁
参数：pkg : u.FredholmPackage；↑u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `FredholmDecomposition.isTopCompl`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module
 𝕜 E] [inst_3 : Topolo…
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `ContinuousLinearMap.FredholmPackage.eq_equiv`：∀ {𝕜 : Type u_1} {E : Type
 u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E
]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.range_projectionOnto`：range_projectionOnto (h : IsCompl p q) :
 range (projectionOnto p q h) = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma FredholmPackage.range_eq {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    u.range = pkg.decCodom.X₁ := by
  simp [pkg.eq_equiv, range_comp]
/-
**ContinuousLinearMap.FredholmPackage.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] {u : E →L[𝕜] F} (pkg : u.FredholmPackage), Set.MapsTo ⇑u ↑
pkg.decDom.X₁ ↑pkg.decCodom.X₁
参数：pkg : u.FredholmPackage。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_range`：mapsTo_range (f : α -> β) (s : Set α) : MapsTo f s (ra
nge f)
-/
lemma FredholmPackage.mapsTo {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    MapsTo u pkg.decDom.X₁ pkg.decCodom.X₁ := by
  simpa [← FredholmPackage.range_eq, LinearMap.coe_range] using Set.mapsTo_range _ _
/-
**ContinuousLinearMap.FredholmPackage.equiv_eq_restrict** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] {u : E →L[𝕜] F} (pkg : u.FredholmPackage), ↑pkg.equiv = u.
restrict ⋯
参数：pkg : u.FredholmPackage。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.FredholmPackage.mapsTo`：∀ {𝕜 : Type u_1} {E : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E] 
  [inst_2 : AddCommGroup F] [ins…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.FredholmPackage.eq_equiv`：∀ {𝕜 : Type u_1} {E : Type
 u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E
]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.restrict.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_
2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}
   {M₂ : Type u_5} [inst_2 : …
· 使用定理 `Submodule.projectionOntoL_apply_left`：projectionOntoL_apply_left (h : Is
TopCompl p q) (x : p) : p.projectionOntoL q h x = x
· 使用定理 `FredholmDecomposition.isTopCompl`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module
 𝕜 E] [inst_3 : Topolo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma FredholmPackage.equiv_eq_restrict {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    pkg.equiv = u.restrict pkg.mapsTo := by
  ext x
  simp [pkg.eq_equiv]
/-
**ContinuousLinearMap.FredholmPackage.isInvertible_restrict** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] {u : E →L[𝕜] F} (pkg : u.FredholmPackage), (u.restrict ⋯).
IsInvertible
参数：pkg : u.FredholmPackage；u.restrict ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.FredholmPackage.mapsTo`：∀ {𝕜 : Type u_1} {E : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E] 
  [inst_2 : AddCommGroup F] [ins…
· 使用定理 `ContinuousLinearMap.FredholmPackage.equiv_eq_restrict`：∀ {𝕜 : Type u_1} 
{E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCo
mmGroup E]   [inst_2 : AddCommGroup F] [ins…
-/
lemma FredholmPackage.isInvertible_restrict {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    u.restrict pkg.mapsTo |>.IsInvertible :=
  ⟨pkg.equiv, pkg.equiv_eq_restrict⟩

/-- The data of a Fredholm package for `u` determines a canonical quasi-inverse of `u`. -/
/-
**ContinuousLinearMap.FredholmPackage.quasiInverse** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousLinearMap.FredholmPackage`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : AddCommGroup E] →           [inst_2 
: AddCommGroup F] →             [inst_3 : _root_.Module 𝕜 E] →               [in
st_4 : _root_.Module 𝕜 F] →                 [inst_5 : TopologicalSpace E] →     
              [inst_6 : TopologicalSpace F] → {u : E →L[𝕜] F} → u.FredholmPackag
e → F →L[𝕜] E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a Fredholm package for `u` determines a canonical quasi-inverse of `
u`.
-/
def FredholmPackage.quasiInverse {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    F →L[𝕜] E :=
  pkg.decDom.X₁.subtypeL ∘L pkg.equiv.symm ∘L pkg.decCodom.proj

/-- The data of a Fredholm package for `u` determines a canonical quasi-inverse of `u`. -/
/-
**ContinuousLinearMap.FredholmPackage.isQuasiInverse** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] {u : E →L[𝕜] F} (pkg : u.FredholmPackage), (↑pkg.quasiInve
rse).IsQuasiInverse ↑u
参数：pkg : u.FredholmPackage；↑pkg.quasiInverse。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.FredholmPackage.eq_equiv`：∀ {𝕜 : Type u_1} {E : Type
 u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E
]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `FredholmDecomposition.finite_X₀`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst :
 NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用引理 `LinearMap.isQuasiInverse_subtype_projectionOnto`：isQuasiInverse_subtype_
projectionOnto {S T : Submodule K V} [IsNoetherian K T] (hST : IsCompl S T) : Is
QuasiInverse S.subtype (S.projectionO…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `FredholmDecomposition.isTopCompl`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module
 𝕜 E] [inst_3 : Topolo…
· 使用定理 `LinearMap.IsQuasiInverse.comp`：∀ {K : Type u_1} {V : Type u_2} {V₂ : Typ
e u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V]   [inst_2 :
 _root_.Module K V]…
· 使用定理 `LinearEquiv.isQuasiInverse`：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u
_4} [inst : CommRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V]
 [inst_3 : AddCo…
· 使用定理 `LinearMap.IsQuasiInverse.symm`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Ty
pe u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.Module
 K V₂] [inst_3 : Ad…

--- 原说明 ---
The data of a Fredholm package for `u` determines a canonical quasi-inverse of `
u`.
-/
lemma FredholmPackage.isQuasiInverse {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    pkg.quasiInverse.IsQuasiInverse u := by
  nth_rw 2 [pkg.eq_equiv]
  have hdom : IsQuasiInverse pkg.decDom.X₁.subtype pkg.decDom.proj :=
    have := pkg.decDom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  have hcodom : IsQuasiInverse pkg.decCodom.X₁.subtype pkg.decCodom.proj :=
    have := pkg.decCodom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  -- For some reason `exact` and `refine` are slow here!
  apply hdom.comp (pkg.equiv.isQuasiInverse.comp hcodom.symm)

end FredholmPackage

variable [T2Space E] [T2Space F] in
/-- Assume that `u : E →L[𝕜] F` has a continuous quasi-inverse. Then there are closed
subspaces of finite codimensions `E₁` and `F₁` between which `u` induces an isomorphism.

This statement is private because it is superseded by later results: using `isFredholm_tfae`,
you can build a `FredholmPackage` for `u`, and then apply `FredholmPackage.isInvertible_restrict`.
-/
/-
**ContinuousLinearMap.exists_restrict_isInvertible_of_isQuasiInverse** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume that `u : E →L[𝕜] F` has a continuous quasi-inverse. Then there are close
d
subspaces of finite codimensions `E₁` and `F₁` between which `u` induces an isom
orphism.

This statement is private because it is superseded by later results: using `isFr
edholm_tfae`,
you can build a `FredholmPackage` for `u`, and then apply `FredholmPackage.isInv
ertible_restrict`.
-/
private theorem exists_restrict_isInvertible_of_isQuasiInverse {u : E →L[𝕜] F}
    {v : F →L[𝕜] E} (hvu : v.IsQuasiInverse u) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
      IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
      E₁.CoFG ∧ F₁.CoFG ∧
      ∃ h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible := by
  obtain ⟨hvu, huv⟩ := hvu
  rw [IsRightQuasiInverse, Setoid.comm, equiv_iff_eqLocus_coFG] at huv
  rw [IsLeftQuasiInverse, Setoid.comm, equiv_iff_eqLocus_coFG] at hvu
  set E₁ := (ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)
  set F₁ := (ContinuousLinearMap.id 𝕜 F).eqLocus (u ∘L v)
  have u_mapsto : MapsTo u E₁ F₁ := fun x hx ↦ congr(u $hx)
  have v_mapsto : MapsTo v F₁ E₁ := fun x hx ↦ congr(v $hx)
  refine ⟨E₁, F₁, isClosed_eqLocus _ _, isClosed_eqLocus _ _, hvu, huv, u_mapsto, ?_⟩
  refine .of_inverse (g := v.restrict v_mapsto) ?_ ?_
  · ext ⟨x, hx : x = u (v x)⟩
    simp [coe_restrict_apply u_mapsto, coe_restrict_apply v_mapsto, ← hx]
  · ext ⟨x, hx : x = v (u x)⟩
    simp [coe_restrict_apply u_mapsto, coe_restrict_apply v_mapsto, ← hx]

variable [CompleteSpace 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

/-- Assume that `u : E →L[𝕜] F` restricts to an isomorphism between closed finite codimension
subspaces `E₁` and `F₁`. Then `u` is Fredholm.

In fact it is enough to assume that the restriction `E₁ →L[𝕜] F₁` is Fredholm, see
`IsFredholm.of_restrict` (not in Mathlib yet). -/
/-
**ContinuousLinearMap.IsFredholm.of_isInvertible_restrict** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap.IsFredholm`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMu
l 𝕜 E]   [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] {u : E →L[𝕜] F} {E₁ : Su
bmodule 𝕜 E},   IsClosed ↑E₁ →     ∀ [E₁_coFG : E₁.CoFG] {F₁ : Submodule 𝕜 F},  
     IsClosed ↑F₁ →         ∀ [F₁_coFG : F₁.CoFG] (h_mapsto : Set.MapsTo ⇑u ↑E₁ 
↑F₁), (u.restrict h_mapsto).IsInvertible → u.IsFredholm
参数：h_mapsto : Set.MapsTo ⇑u ↑E₁ ↑F₁；u.restrict h_mapsto。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`：∀ {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type u_2} {F : T
ype u_3}   [inst_2 : AddCommGroup E] [inst_3 : _r…
· 使用定理 `Topology.IsEmbedding.isStrictMap`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsEm
bedding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Submodule.isEmbedding_subtype`：isEmbedding_subtype (p : Submodule R M) :
 Topology.IsEmbedding p.subtype
· 使用引理 `IsHomeomorph.isEmbedding`：isEmbedding : IsEmbedding f
· 使用定理 `ContinuousLinearEquiv.isHomeomorph`：isHomeomorph (f : M ≃SL[σ] M₁) : IsH
omeomorph f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.range_comp`：range_comp [RingHomSurjective σ₂₃] [RingHomSurje
ctive σ₁₃] : LinearMap.range (h.comp (e : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = Li
nearMap.rang…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.disjoint_iff_comap_eq_bot`：disjoint_iff_comap_eq_bot {p q : Su
bmodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥
· 使用引理 `LinearMap.ker_domRestrict`：ker_domRestrict (p : Submodule R M) (f : M ->
ₛₗ[τ₁₂] M₂) : ker (domRestrict f p) = (ker f).comap p.subtype
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.fg_iff_finiteDimensional`：fg_iff_finiteDimensional (s : Submod
ule K V) : s.FG ↔ FiniteDimensional K s
· 使用定理 `Submodule.CoFG.fg_of_disjoint`：∀ {R : Type u_1} [inst : Ring R] {M : Typ
e u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsNoetherianRin
g R] {S T : Submodu…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Submodule.CoFG.of_le`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Submodule R M}, S 
≤ T → S.Co…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that `u : E →L[𝕜] F` restricts to an isomorphism between closed finite co
dimension
subspaces `E₁` and `F₁`. Then `u` is Fredholm.

In fact it is enough to assume that the restriction `E₁ →L[𝕜] F₁` is Fredholm, s
ee
`IsFredholm.of_restrict` (not in Mathlib yet).
-/
theorem IsFredholm.of_isInvertible_restrict {u : E →L[𝕜] F}
    {E₁ : Submodule 𝕜 E} (E₁_closed : IsClosed (E₁ : Set E)) [E₁_coFG : E₁.CoFG]
    {F₁ : Submodule 𝕜 F} (F₁_closed : IsClosed (F₁ : Set F)) [F₁_coFG : F₁.CoFG]
    (h_mapsto : MapsTo u E₁ F₁) (h_inv : (u.restrict h_mapsto).IsInvertible) :
    IsFredholm u := by
  obtain ⟨e, he⟩ := h_inv
  have eqL : u.domRestrict E₁ = F₁.subtypeL ∘L e := congr(F₁.subtypeL ∘L $he).symm
  have eqₗ : u.toLinearMap.domRestrict E₁ = F₁.subtype ∘ₗ e := congr(($eqL).toLinearMap)
  have h : Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
    rw [u.isStrictMap_isClosed_range_iff_restrict E₁ E₁_closed, eqL]
    exact ⟨F₁.isEmbedding_subtype.comp e.isHomeomorph.isEmbedding |>.isStrictMap, by simpa⟩
  have disj : Disjoint E₁ u.ker := by
    rw [disjoint_iff_comap_eq_bot, ← LinearMap.ker_domRestrict, eqₗ,
      LinearMap.ker_comp, ker_subtype, comap_bot, LinearEquiv.ker]
  refine ⟨h.1, h.2, ?_, ?_, ?_⟩
  · rw [← Submodule.fg_iff_finiteDimensional]
    exact E₁_coFG.fg_of_disjoint disj.symm
  · refine F₁_coFG.of_le (le_trans ?_ (u.range_domRestrict_le_range E₁))
    rw [eqₗ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, range_subtype]
  · exact .of_disjoint_of_finiteDimensional_quotient E₁_closed disj.symm

omit [ContinuousSMul 𝕜 E] in
/-- Let `u : E →L[𝕜] F` be a Fredholm operator. Given `dom₁` (resp. `codom₀`) an arbitrary
topological complement of `u.ker` (resp. `u.range`), we get a `FredholmPackage` for `u`
by considering the decompositions `E = dom₁ ⊕ u.ker`, `F = u.range ⊕ codom₀`, and the isomorphism
`dom₁ ≃L[𝕜] u.range` induced by `u`.

If you need control over the decompositions, this is the primary way to get a `FredholmPackage`.
Otherwise, see `IsFredholm.nonempty_fredholmPackage`. -/
/-
**ContinuousLinearMap.IsFredholm.fredholmPackage** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousLinearMap.IsFredholm`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : AddCommGroup E] →           [inst_2 
: AddCommGroup F] →             [inst_3 : _root_.Module 𝕜 E] →               [in
st_4 : _root_.Module 𝕜 F] →                 [inst_5 : TopologicalSpace E] →     
              [inst_6 : TopologicalSpace F] →                     [IsTopological
AddGroup E] →                       {u : E →L[𝕜] F} →                         u.
IsFredholm →                           {dom₁ : Submodule 𝕜 E} →                 
            {codom₀ : Submodule 𝕜 F} →                               Submodule.I
sTopCompl (↑u).ker dom₁ →                                 Submodule.IsTopCompl (
↑u).range codom₀ → u.FredholmPackage
参数：↑u；↑u。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsFredholm.finite_ker`：∀ {𝕜 : Type u_1} {E : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]  
 [inst_2 : AddCommGroup F] [ins…
· 使用定理 `ContinuousLinearMap.IsFredholm.isStrictMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E] 
  [inst_2 : AddCommGroup F] [ins…

--- 原说明 ---
Let `u : E →L[𝕜] F` be a Fredholm operator. Given `dom₁` (resp. `codom₀`) an arb
itrary
topological complement of `u.ker` (resp. `u.range`), we get a `FredholmPackage` 
for `u`
by considering the decompositions `E = dom₁ ⊕ u.ker`, `F = u.range ⊕ codom₀`, an
d the isomorphism
`dom₁ ≃L[𝕜] u.range` induced by `u`.

If you need control over the decompositions, this is the primary way to get a `F
redholmPackage`.
Otherwise, see `IsFredholm.nonempty_fredholmPackage`.
-/
def IsFredholm.fredholmPackage {u : E →L[𝕜] F}
    (u_fred : IsFredholm u) {dom₁ : Submodule 𝕜 E} {codom₀ : Submodule 𝕜 F}
    (h_dom : IsTopCompl u.ker dom₁) (h_codom : IsTopCompl u.range codom₀) :
    FredholmPackage u where
  decDom :=
    { X₀ := u.ker
      X₁ := dom₁
      isTopCompl := h_dom.symm
      finite_X₀ := u_fred.finite_ker }
  decCodom :=
    { X₀ := codom₀
      X₁ := u.range
      isTopCompl := h_codom
      finite_X₀ := .of_fg <| u_fred.finite_coker.fg_of_isCompl h_codom.isCompl }
  equiv :=
    letI Φ : dom₁ ≃L[𝕜] E ⧸ u.ker := u.ker.quotientEquivOfIsTopCompl dom₁ h_dom |>.symm
    letI Ψ : (E ⧸ u.ker) ≃L[𝕜] u.range := .quotKerEquivRange u_fred.isStrictMap
    Φ.trans Ψ
  eq_equiv := by
    refine LinearMap.ext_on_codisjoint h_dom.isCompl.codisjoint ?_ ?_
    · intro x (hx : u x = 0)
      simp [hx, projection_apply_of_mem_right]
    · intro x (hx : x ∈ dom₁)
      simp [hx, projection_apply_of_mem_left, ContinuousLinearEquiv.quotKerEquivRange]

omit [ContinuousSMul 𝕜 E] in
/-- Every Fredholm operator admits a `FredholmPackage`.

This is the primary way to get a `FredholmPackage` if you don't need control of the decompositions.
If you do, see `IsFredholm.fredholmPackage`. -/
/-
**ContinuousLinearMap.IsFredholm.nonempty_fredholmPackage** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap.IsFredholm`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [IsTopological
AddGroup F]   [ContinuousSMul 𝕜 F] {u : E →L[𝕜] F}, u.IsFredholm → Nonempty u.Fr
edholmPackage
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ClosedComplemented.exists_isTopCompl`：∀ {R : Type u_1} [inst :
 Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] {p : …
· 使用定理 `ContinuousLinearMap.IsFredholm.closedComplemented_range`：∀ {𝕜 : Type u_1
} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : Add
CommGroup E]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `ContinuousLinearMap.IsFredholm.closedComplemented_ker`：∀ {𝕜 : Type u_1} 
{E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCo
mmGroup E]   [inst_2 : AddCommGroup F] [ins…

--- 原说明 ---
Every Fredholm operator admits a `FredholmPackage`.

This is the primary way to get a `FredholmPackage` if you don't need control of 
the decompositions.
If you do, see `IsFredholm.fredholmPackage`.
-/
theorem IsFredholm.nonempty_fredholmPackage {u : E →L[𝕜] F}
    (u_fred : IsFredholm u) : Nonempty (FredholmPackage u) := by
  obtain ⟨codom₀, h_codom⟩ := u_fred.closedComplemented_range.exists_isTopCompl
  obtain ⟨dom₁, h_dom⟩ := u_fred.closedComplemented_ker.exists_isTopCompl
  exact ⟨u_fred.fredholmPackage h_dom h_codom⟩

variable [T2Space E] [T2Space F]

/--
Let `E`, `F` be two Hausdorff topological vector spaces over a complete `NontriviallyNormedField`
denoted `𝕜`, and `u : E →L[𝕜] F` a continuous linear map. The following conditions are equivalent:

1. `u` is a **Fredholm operator**, in the sense of `ContinuousLinearMap.IsFredholm`.
2. `u` admits a continuous **quasi-inverse**, in the sense of `LinearMap.IsQuasiInverse`.
3. There are closed finite-codimension subspaces `E₁` and `F₁` of `E` and `F` between which `u`
  induces an isomorphism.
4. `u` admits a `FredholmPackage`.

In practice, condition `4` is the "strongest", so you should probably not use it to *prove* that an
operator is Fredholm.
-/
/-
**ContinuousLinearMap.isFredholm_tfae** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：isFredholm_tfae (u : E ->L[𝕜] F) : [ IsFredholm u, exists v : F ->L[𝕜] E, 
v.IsQuasiInverse u, exists (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed (
E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧ E₁.CoFG ∧ F₁.CoFG ∧ exists h : MapsTo u E₁
 F₁, (u.restrict h).IsInvertible, Nonempty (FredholmPackage u) ].TFAE
参数：u : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsFredholm.nonempty_fredholmPackage`：∀ {𝕜 : Type u_1
} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : Add
CommGroup E]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `ContinuousLinearMap.FredholmPackage.isQuasiInverse`：∀ {𝕜 : Type u_1} {E 
: Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommG
roup E]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `_private.Mathlib.Analysis.Normed.Operator.Fredholm.Basic.0.ContinuousLin
earMap.exists_restrict_isInvertible_of_isQuasiInverse`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup 
E]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict`：∀ {𝕜 : Type u_1
} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : Add
CommGroup E]   [inst_2 : AddCommGroup F] [ins…
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
Let `E`, `F` be two Hausdorff topological vector spaces over a complete `Nontriv
iallyNormedField`
denoted `𝕜`, and `u : E →L[𝕜] F` a continuous linear map. The following conditio
ns are equivalent:

1. `u` is a **Fredholm operator**, in the sense of `ContinuousLinearMap.IsFredho
lm`.
2. `u` admits a continuous **quasi-inverse**, in the sense of `LinearMap.IsQuasi
Inverse`.
3. There are closed finite-codimension subspaces `E₁` and `F₁` of `E` and `F` be
tween which `u`
  induces an isomorphism.
4. `u` admits a `FredholmPackage`.

In practice, condition `4` is the "strongest", so you should probably not use it
 to *prove* that an
operator is Fredholm.
-/
theorem isFredholm_tfae (u : E →L[𝕜] F) :
    [ IsFredholm u,
      ∃ v : F →L[𝕜] E, v.IsQuasiInverse u,
      ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
        IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
        E₁.CoFG ∧ F₁.CoFG ∧
        ∃ h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible,
      Nonempty (FredholmPackage u) ].TFAE := by
  tfae_have 1 → 4 := IsFredholm.nonempty_fredholmPackage
  tfae_have 4 → 2 := by
    rintro ⟨dec⟩
    exact ⟨dec.quasiInverse, dec.isQuasiInverse⟩
  tfae_have 2 → 3 := by
    rintro ⟨v, huv⟩
    exact exists_restrict_isInvertible_of_isQuasiInverse huv
  tfae_have 3 → 1 := by
    rintro ⟨E₁, F₁, E₁_closed, F₁_closed, E₁_coFG, F₁_coFG, u_mapsto, u_invertible⟩
    exact .of_isInvertible_restrict E₁_closed F₁_closed u_mapsto u_invertible
  tfae_finish

/-- If `u` has a Fredholm package, it is Fredholm. -/
/-
**ContinuousLinearMap.FredholmPackage.isFredholm** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap.FredholmPackage`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMu
l 𝕜 E]   [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space E] [T2Space F] 
{u : E →L[𝕜] F} (pkg : u.FredholmPackage),   u.IsFredholm
参数：pkg : u.FredholmPackage。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `ContinuousLinearMap.isFredholm_tfae`：isFredholm_tfae (u : E ->L[𝕜] F) : 
[ IsFredholm u, exists v : F ->L[𝕜] E, v.IsQuasiInverse u, exists (E₁ : Submodul
e 𝕜 E) (F₁ : Submodule 𝕜 …

--- 原说明 ---
If `u` has a Fredholm package, it is Fredholm.
-/
theorem FredholmPackage.isFredholm {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    IsFredholm u :=
  isFredholm_tfae u |>.out 3 0 |>.mp (Nonempty.intro pkg)
/-
**ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：isFredholm_iff_exists_isQuasiInverse {u : E ->L[𝕜] F} : IsFredholm u ↔ exi
sts v : F ->L[𝕜] E, v.IsQuasiInverse u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `ContinuousLinearMap.isFredholm_tfae`：isFredholm_tfae (u : E ->L[𝕜] F) : 
[ IsFredholm u, exists v : F ->L[𝕜] E, v.IsQuasiInverse u, exists (E₁ : Submodul
e 𝕜 E) (F₁ : Submodule 𝕜 …
-/
theorem isFredholm_iff_exists_isQuasiInverse {u : E →L[𝕜] F} :
    IsFredholm u ↔ ∃ v : F →L[𝕜] E, v.IsQuasiInverse u :=
  isFredholm_tfae u |>.out 0 1

alias ⟨IsFredholm.exists_isQuasiInverse, _⟩ := isFredholm_iff_exists_isQuasiInverse
/-
**ContinuousLinearMap.IsFredholm.of_isQuasiInverse** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap.IsFredholm`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : AddCommGroup F] [inst_3 : _root_.M
odule 𝕜 E] [inst_4 : _root_.Module 𝕜 F] [inst_5 : TopologicalSpace E]   [inst_6 
: TopologicalSpace F] [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMu
l 𝕜 E]   [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space E] [T2Space F] 
{u : E →L[𝕜] F} {v : F →L[𝕜] E},   (↑v).IsQuasiInverse ↑u → u.IsFredholm
参数：↑v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse`：isFredholm_iff
_exists_isQuasiInverse {u : E ->L[𝕜] F} : IsFredholm u ↔ exists v : F ->L[𝕜] E, 
v.IsQuasiInverse u
-/
theorem IsFredholm.of_isQuasiInverse {u : E →L[𝕜] F} {v : F →L[𝕜] E} (h : v.IsQuasiInverse u) :
    IsFredholm u :=
  isFredholm_iff_exists_isQuasiInverse.mpr ⟨v, h⟩

end DefTFAE

end TVS
end ContinuousLinearMap

end

