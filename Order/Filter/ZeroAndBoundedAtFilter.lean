/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Algebra.Algebra.Pi

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `ZeroAtFilter` as well as being
`BoundedAtFilter`. Alongside this we construct the `Submodule`, `AddSubmonoid` of functions
that are `ZeroAtFilter`. Similarly, we construct the `Submodule` and `Subalgebra` of functions
that are `BoundedAtFilter`.

-/

@[expose] public section


namespace Filter

variable {𝕜 α β : Type*}

open Topology

/--
Definition of `ZeroAtFilter` / `ZeroAtFilter` 的定义

English:
definition ZeroAtFilter
  signature: [Zero β] [TopologicalSpace β] (l : Filter α) (f : α -> β)
  body: Filter.Tendsto f l (𝓝 0)

中文:
定义 ZeroAtFilter
  签名: [Zero β] [TopologicalSpace β] (l : Filter α) (f : α -> β)
  定义体: Filter.Tendsto f l (𝓝 0)

Depends on / 依赖: Filter, Filter.Tendsto, Tendsto
-/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α -> β) : Prop :=
  Filter.Tendsto f l (𝓝 0)

/--
theorem `zero_zeroAtFilter` / 定理 `zero_zeroAtFilter`

English:
theorem zero_zeroAtFilter
  given: [Zero β] [TopologicalSpace β] (l : Filter α)
  proof: tendsto_const_nhds

nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α -> β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using! hf.add hg

nonrec theorem ZeroAtFilter.neg [TopologicalSpace

中文:
定理 zero_zeroAtFilter
  条件: [Zero β] [TopologicalSpace β] (l : Filter α)
  证明: tendsto_const_nhds

nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α -> β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using! hf.add hg

nonrec theorem ZeroAtFilter.neg [TopologicalSpace

Depends on / 依赖: tendsto_const_nhds
-/
theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α -> β) :=
  tendsto_const_nhds

nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α -> β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using! hf.add hg

nonrec theorem ZeroAtFilter.neg [TopologicalSpace β] [SubtractionMonoid β] [ContinuousNeg β]
    {l : Filter α} {f : α -> β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by
  simpa using! hf.neg

/--
theorem `ZeroAtFilter.smul` / 定理 `ZeroAtFilter.smul`

English:
theorem ZeroAtFilter.smul
  statement: [TopologicalSpace β] [Zero β]
  proof: by simpa using! hf.const_smul c

中文:
定理 ZeroAtFilter.smul
  结论: [TopologicalSpace β] [Zero β]
  证明: by simpa using! hf.const_smul c

Depends on / 依赖: const_smul, hf.const_smul
-/
theorem ZeroAtFilter.smul [TopologicalSpace β] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousConstSMul 𝕜 β] {l : Filter α} {f : α -> β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using! hf.const_smul c

variable (𝕜) in
/--
Definition of `zeroAtFilterSubmodule` / `zeroAtFilterSubmodule` 的定义

English:
definition zeroAtFilterSubmodule
  body: {f | ZeroAtFilter l f}
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c

中文:
定义 zeroAtFilterSubmodule
  定义体: {f | ZeroAtFilter l f}
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c

Depends on / 依赖: ZeroAtFilter
-/
def zeroAtFilterSubmodule
    [TopologicalSpace β] [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β]
    [ContinuousAdd β] [ContinuousConstSMul 𝕜 β]
    (l : Filter α) : Submodule 𝕜 (α -> β) where
  carrier := {f | ZeroAtFilter l f}
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c

/--
Definition of `zeroAtFilterAddSubmonoid` / `zeroAtFilterAddSubmonoid` 的定义

English:
definition zeroAtFilterAddSubmonoid
  signature: [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
  body: {f | ZeroAtFilter l f}
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l

中文:
定义 zeroAtFilterAddSubmonoid
  签名: [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
  定义体: {f | ZeroAtFilter l f}
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l

Depends on / 依赖: ZeroAtFilter
-/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α -> β) where
  carrier := {f | ZeroAtFilter l f}
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l

/--
Definition of `BoundedAtFilter` / `BoundedAtFilter` 的定义

English:
definition BoundedAtFilter
  signature: [Norm β] (l : Filter α) (f : α -> β)
  body: Asymptotics.IsBigO l f (1 : α -> Real)

中文:
定义 BoundedAtFilter
  签名: [Norm β] (l : Filter α) (f : α -> β)
  定义体: Asymptotics.IsBigO l f (1 : α -> Real)

Depends on / 依赖: Asymptotics, Asymptotics.IsBigO, IsBigO
-/
def BoundedAtFilter [Norm β] (l : Filter α) (f : α -> β) : Prop :=
  Asymptotics.IsBigO l f (1 : α -> Real)

/--
theorem `ZeroAtFilter.boundedAtFilter` / 定理 `ZeroAtFilter.boundedAtFilter`

English:
theorem ZeroAtFilter.boundedAtFilter
  statement: [SeminormedAddGroup β] {l : Filter α} {f : α -> β}
  proof: ((Asymptotics.isLittleO_one_iff _).mpr hf).isBigO

中文:
定理 ZeroAtFilter.boundedAtFilter
  结论: [SeminormedAddGroup β] {l : Filter α} {f : α -> β}
  证明: ((Asymptotics.isLittleO_one_iff _).mpr hf).isBigO

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_one_iff, Quotient, Quotient.mk, _surjective, isBigO, isLittleO_one_iff
-/
theorem ZeroAtFilter.boundedAtFilter [SeminormedAddGroup β] {l : Filter α} {f : α -> β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f :=
  ((Asymptotics.isLittleO_one_iff _).mpr hf).isBigO

/--
theorem `const_boundedAtFilter` / 定理 `const_boundedAtFilter`

English:
theorem const_boundedAtFilter
  given: [Norm β] (l : Filter α) (c : β)
  proof: Asymptotics.isBigO_const_const c one_ne_zero l

中文:
定理 const_boundedAtFilter
  条件: [Norm β] (l : Filter α) (c : β)
  证明: Asymptotics.isBigO_const_const c one_ne_zero l

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_const_const, isBigO_const_const, one_ne_zero
-/
theorem const_boundedAtFilter [Norm β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α -> β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l

-- TODO(https://github.com/leanprover-community/mathlib4/issues/19288): Remove all Comm in the next
-- three lemmas. This would require modifying the corresponding general asymptotics lemma.
nonrec theorem BoundedAtFilter.add [SeminormedAddCommGroup β] {l : Filter α} {f g : α -> β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using! hf.add hg

/--
theorem `BoundedAtFilter.neg` / 定理 `BoundedAtFilter.neg`

English:
theorem BoundedAtFilter.neg
  statement: [SeminormedAddCommGroup β] {l : Filter α} {f : α -> β}
  proof: hf.neg_left

中文:
定理 BoundedAtFilter.neg
  结论: [SeminormedAddCommGroup β] {l : Filter α} {f : α -> β}
  证明: hf.neg_left

Depends on / 依赖: hf.neg_left, neg_left
-/
theorem BoundedAtFilter.neg [SeminormedAddCommGroup β] {l : Filter α} {f : α -> β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left

/--
theorem `BoundedAtFilter.smul` / 定理 `BoundedAtFilter.smul`

English:
theorem BoundedAtFilter.smul
  proof: hf.const_smul_left c

nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α -> β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert! Asymptotics.isBigO_refl (E := Real) _ l
  simp

中文:
定理 BoundedAtFilter.smul
  证明: hf.const_smul_left c

nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α -> β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert! Asymptotics.isBigO_refl (E := Real) _ l
  simp

Depends on / 依赖: const_smul_left, hf.const_smul_left
-/
theorem BoundedAtFilter.smul
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
    {l : Filter α} {f : α -> β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c

nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α -> β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert! Asymptotics.isBigO_refl (E := Real) _ l
  simp

/--
theorem `ZeroAtFilter.mul_boundedAtFilter` / 定理 `ZeroAtFilter.mul_boundedAtFilter`

English:
theorem ZeroAtFilter.mul_boundedAtFilter
  statement: [SeminormedRing β] {l : Filter α}
  proof: by
  rw [ZeroAtFilter]; rw [← Asymptotics.isLittleO_one_iff (F := Real)] at hf ⊢
  simpa using! hf.mul_isBigO hg

中文:
定理 ZeroAtFilter.mul_boundedAtFilter
  结论: [SeminormedRing β] {l : Filter α}
  证明: by
  rw [ZeroAtFilter]; rw [← Asymptotics.isLittleO_one_iff (F := Real)] at hf ⊢
  simpa using! hf.mul_isBigO hg

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_one_iff, ZeroAtFilter, hf.mul_isBigO, isLittleO_one_iff, mul_isBigO
-/
theorem ZeroAtFilter.mul_boundedAtFilter [SeminormedRing β] {l : Filter α}
    {f g : α -> β} (hf : ZeroAtFilter l f) (hg : BoundedAtFilter l g) : ZeroAtFilter l (f * g) := by
  rw [ZeroAtFilter]; rw [← Asymptotics.isLittleO_one_iff (F := Real)] at hf ⊢
  simpa using! hf.mul_isBigO hg

/--
theorem `BoundedAtFilter.mul_zeroAtFilter` / 定理 `BoundedAtFilter.mul_zeroAtFilter`

English:
theorem BoundedAtFilter.mul_zeroAtFilter
  statement: [SeminormedRing β] {l : Filter α}
  proof: by
  rw [ZeroAtFilter]; rw [← Asymptotics.isLittleO_one_iff (F := Real)] at hg ⊢
  simpa using! hf.mul_isLittleO hg

中文:
定理 BoundedAtFilter.mul_zeroAtFilter
  结论: [SeminormedRing β] {l : Filter α}
  证明: by
  rw [ZeroAtFilter]; rw [← Asymptotics.isLittleO_one_iff (F := Real)] at hg ⊢
  simpa using! hf.mul_isLittleO hg

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_one_iff, ZeroAtFilter, hf.mul_isLittleO, isLittleO_one_iff, mul_isLittleO
-/
theorem BoundedAtFilter.mul_zeroAtFilter [SeminormedRing β] {l : Filter α}
    {f g : α -> β} (hf : BoundedAtFilter l f) (hg : ZeroAtFilter l g) : ZeroAtFilter l (f * g) := by
  rw [ZeroAtFilter]; rw [← Asymptotics.isLittleO_one_iff (F := Real)] at hg ⊢
  simpa using! hf.mul_isLittleO hg

variable (𝕜) in
/--
Definition of `boundedFilterSubmodule` / `boundedFilterSubmodule` 的定义

English:
definition boundedFilterSubmodule
  body: {f | BoundedAtFilter l f}
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c

中文:
定义 boundedFilterSubmodule
  定义体: {f | BoundedAtFilter l f}
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c

Depends on / 依赖: BoundedAtFilter
-/
def boundedFilterSubmodule
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) :
    Submodule 𝕜 (α -> β) where
  carrier := {f | BoundedAtFilter l f}
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c

variable (𝕜) in
/--
Definition of `boundedFilterSubalgebra` / `boundedFilterSubalgebra` 的定义

English:
definition boundedFilterSubalgebra
  body: Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg => by simpa only [Pi.one_apply, mul_one, norm_mul] using! hf.mul hg)

中文:
定义 boundedFilterSubalgebra
  定义体: Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg => by simpa only [Pi.one_apply, mul_one, norm_mul] using! hf.mul hg)

Depends on / 依赖: Pi.one_apply, Submodule, Submodule.toSubalgebra, boundedFilterSubmodule, const_boundedAtFilter, hf.mul, mul_one, norm_mul, one_apply, toSubalgebra
-/
def boundedFilterSubalgebra
    [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) :
    Subalgebra 𝕜 (α -> β) :=
  Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg => by simpa only [Pi.one_apply, mul_one, norm_mul] using! hf.mul hg)

/--
theorem `BoundedAtFilter.prod` / 定理 `BoundedAtFilter.prod`

English:
theorem BoundedAtFilter.prod
  statement: {ι : Type} (s : Finset ι) [SeminormedCommRing β]
  proof: (boundedFilterSubalgebra β l).prod_mem (f := f) h

中文:
定理 BoundedAtFilter.prod
  结论: {ι : Type} (s : Finset ι) [SeminormedCommRing β]
  证明: (boundedFilterSubalgebra β l).prod_mem (f := f) h

Depends on / 依赖: boundedFilterSubalgebra, prod_mem
-/
theorem BoundedAtFilter.prod {ι : Type} (s : Finset ι) [SeminormedCommRing β]
    {l : Filter α} {f : ι -> α -> β} (h : forall i in s, BoundedAtFilter l (f i)) :
    BoundedAtFilter l (∏ i in s, f i) :=
  (boundedFilterSubalgebra β l).prod_mem (f := f) h

end Filter
