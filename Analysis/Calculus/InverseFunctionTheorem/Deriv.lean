/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, 1D case

In this file we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `ContinuousLinearEquiv.unitsEquivAut` to translate `HasStrictDerivAt f f' a` and
`f' ≠ 0` into `HasStrictFDerivAt f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (f : 𝕜 → 𝕜)

noncomputable section
namespace HasStrictDerivAt

variable (f' a : 𝕜) (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)
include hf hf'

/-- A function that is inverse to `f` near `a`. -/
/-
**HasStrictDerivAt.localInverse** 是 Mathlib 中的一个缩写定义，位于命名空间 `HasStrictDerivAt`。
形式化陈述：localInverse : 𝕜 -> 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…

--- 原说明 ---
A function that is inverse to `f` near `a`.
-/
abbrev localInverse : 𝕜 → 𝕜 :=
  (hf.hasStrictFDerivAt_equiv hf').localInverse _ _ _

variable {f f' a}
/-
**HasStrictDerivAt.eventually_left_inverse** 是 Mathlib 中的一个引理，位于命名空间 `HasStrictD
erivAt`。
形式化陈述：eventually_left_inverse : forallᶠ x in 𝓝 a, localInverse f f' a hf hf' (f 
x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.eventually_left_inverse`：eventually_left_inverse (hf :
 HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ x in 𝓝 a, hf.localInverse f 
f' a (f x) = x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
-/
lemma eventually_left_inverse : ∀ᶠ x in 𝓝 a, localInverse f f' a hf hf' (f x) = x :=
  HasStrictFDerivAt.eventually_left_inverse ..
/-
**HasStrictDerivAt.eventually_right_inverse** 是 Mathlib 中的一个引理，位于命名空间 `HasStrict
DerivAt`。
形式化陈述：eventually_right_inverse : forallᶠ x in 𝓝 (f a), f (localInverse f f' a hf
 hf' x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.eventually_right_inverse`：eventually_right_inverse (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ y in 𝓝 (f a), f (hf.localI
nverse f f' a y) = y
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
-/
lemma eventually_right_inverse : ∀ᶠ x in 𝓝 (f a), f (localInverse f f' a hf hf' x) = x :=
  HasStrictFDerivAt.eventually_right_inverse ..
/-
**HasStrictDerivAt.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictDerivAt`。
形式化陈述：map_nhds_eq : map f (𝓝 a) = 𝓝 (f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.map_nhds_eq_of_equiv`：map_nhds_eq_of_equiv (hf : HasSt
rictFDerivAt f (f' : E ->L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a)
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
-/
theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').map_nhds_eq_of_equiv
/-
**HasStrictDerivAt.to_localInverse** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictDerivAt`。
形式化陈述：to_localInverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.to_localInverse`：to_localInverse (hf : HasStrictFDeriv
At f (f' : E ->L[𝕜] F) a) : HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm 
: F ->L[𝕜] E) (f a)
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
-/
theorem to_localInverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_localInverse
/-
**HasStrictDerivAt.to_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictDer
ivAt`。
形式化陈述：to_local_left_inverse {g : 𝕜 -> 𝕜} (hg : forallᶠ x in 𝓝 a, g (f x) = x) : 
HasStrictDerivAt g f'⁻¹ (f a)
参数：hg : forallᶠ x in 𝓝 a, g (f x) = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.to_local_left_inverse`：to_local_left_inverse (hf : Has
StrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E} (hg : forallᶠ x in 𝓝 a, g (f 
x) = x) : HasStrictFDerivAt g…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
-/
theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    HasStrictDerivAt g f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_local_left_inverse hg

end HasStrictDerivAt

variable {f}

/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
/-
**isOpenMap_of_hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_of_hasStrictDerivAt {f' : 𝕜 -> 𝕜} (hf : forall x, HasStrictDeriv
At f (f' x) x) (h0 : forall x, f' x != 0) : IsOpenMap f
参数：hf : forall x, HasStrictDerivAt f (f' x) x；h0 : forall x, f' x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpenMap_iff_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X),
 nhds (f x)…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `HasStrictDerivAt.map_nhds_eq`：map_nhds_eq : map f (𝓝 a) = 𝓝 (f a)

--- 原说明 ---
If a function has a non-zero strict derivative at all points, then it is an open
 map.
-/
theorem isOpenMap_of_hasStrictDerivAt {f' : 𝕜 → 𝕜}
    (hf : ∀ x, HasStrictDerivAt f (f' x) x) (h0 : ∀ x, f' x ≠ 0) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).ge
