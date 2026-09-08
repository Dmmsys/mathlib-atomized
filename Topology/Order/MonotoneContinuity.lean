/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Continuity of monotone functions

In this file we prove the following fact: if `f` is a monotone function on a neighborhood of `a`
and the image of this neighborhood is a neighborhood of `f a`, then `f` is continuous at `a`, see
`continuousWithinAt_of_monotoneOn_of_image_mem_nhds`, as well as several similar facts.

We also prove that an `OrderIso` is continuous.

## Tags

continuous, monotone
-/

public section


open Set Filter

open Topology

section LinearOrder

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [LinearOrder β] [TopologicalSpace β] [OrderTopology β]

/-- If `f` is a function strictly monotone on a right neighborhood of `a` and the
image of this neighborhood under `f` meets every interval `(f a, b]`, `b > f a`, then `f` is
continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x ≤ 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
/-
**StrictMonoOn.continuousWithinAt_right_of_exists_between** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_right_of_exists_between {f : α -> β} {s : 
Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hfs : forall b >
 f a, exists c in s, f c in Ioc (f a) b) : ContinuousWithinAt f (Ici a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[>=] a；hfs : forall b > f a, exists c in
 s, f c in Ioc (f a) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Ico_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ico b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b

--- 原说明 ---
If `f` is a function strictly monotone on a right neighborhood of `a` and the
image of this neighborhood under `f` meets every interval `(f a, b]`, `b > f a`,
 then `f` is
continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` is required because
 otherwise the
function `f : ℝ → ℝ` given by `f x = if x ≤ 0 then x else x + 1` would be a coun
ter-example at
`a = 0`.
-/
theorem StrictMonoOn.continuousWithinAt_right_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have has : a ∈ s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      ((h_mono.le_iff_le has hxs).2 hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    rw [h_mono.lt_iff_lt has hcs] at hac
    filter_upwards [hs, Ico_mem_nhdsGE hac]
    rintro x hx ⟨_, hxc⟩
    exact ((h_mono.lt_iff_lt hx hcs).2 hxc).trans_le hcb

/-- If `f` is a monotone function on a right neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(f a, b)`, `b > f a`, then `f` is continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b` cannot be replaced by the weaker
assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` we use for strictly monotone functions
because otherwise the function `ceil : ℝ → ℤ` would be a counter-example at `a = 0`. -/
/-
**continuousWithinAt_right_of_monotoneOn_of_exists_between** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：continuousWithinAt_right_of_monotoneOn_of_exists_between {f : α -> β} {s :
 Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝[>=] a) (hfs : forall b > 
f a, exists c in s, f c in Ioo (f a) b) : ContinuousWithinAt f (Ici a) a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝[>=] a；hfs : forall b > f a, exists c in s
, f c in Ioo (f a) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ico_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ico b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is a monotone function on a right neighborhood of `a` and the image of th
is neighborhood
under `f` meets every interval `(f a, b)`, `b > f a`, then `f` is continuous at 
`a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b` cannot be replaced 
by the weaker
assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` we use for strictly mon
otone functions
because otherwise the function `ceil : ℝ → ℤ` would be a counter-example at `a =
 0`.
-/
theorem continuousWithinAt_right_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have has : a ∈ s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      (h_mono has hxs hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    have : a < c := not_le.1 fun h => hac.not_ge <| h_mono hcs has h
    filter_upwards [hs, Ico_mem_nhdsGE this]
    rintro x hx ⟨_, hxc⟩
    exact (h_mono hx hcs hxc.le).trans_lt hcb

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f`
is continuous at `a` from the right. -/
/-
**continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [De
nselyOrdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs :
 s in 𝓝[>=] a) (hfs : closure (f '' s) in 𝓝[>=] f a) : ContinuousWithinAt f (Ici
 a) a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝[>=] a；hfs : closure (f '' s) in 𝓝[>=] f a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_exists_between`：continuousWith
inAt_right_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_m
ono : MonotoneOn f s) (hs : s in 𝓝[>=] a) (hfs…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset`：mem_nhdsGE_iff_exists_mem_Ioc_
Ico_subset {a u' : α} {s : Set α} (hu' : a < u') : s in 𝓝[>=] a ↔ exists u in Io
c a u', Ico a u subseteq s
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c

--- 原说明 ---
If a function `f` with a densely ordered codomain is monotone on a right neighbo
rhood of `a` and
the closure of the image of this neighborhood under `f` is a right neighborhood 
of `f a`, then `f`
is continuous at `a` from the right.
-/
theorem continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : closure (f '' s) ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a := by
  refine continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono hs fun b hb => ?_
  rcases (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
  rcases exists_between hab' with ⟨c', hc'⟩
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') isOpen_Ioo hc' with
    ⟨_, hc, ⟨c, hcs, rfl⟩⟩
  exact ⟨c, hcs, hc.1, hc.2.trans_le hbb'⟩

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is continuous at
`a` from the right. -/
/-
**continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrd
ered β] {f : α -> β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝[
>=] a) (hfs : f '' s in 𝓝[>=] f a) : ContinuousWithinAt f (Ici a) a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝[>=] a；hfs : f '' s in 𝓝[>=] f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin`：
continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyO
rdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : Monoton…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If a function `f` with a densely ordered codomain is monotone on a right neighbo
rhood of `a` and
the image of this neighborhood under `f` is a right neighborhood of `f a`, then 
`f` is continuous at
`a` from the right.
-/
theorem continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : f '' s ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs <|
    mem_of_superset hfs subset_closure

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`,
then `f` is continuous at `a` from the right. -/
/-
**StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin** 是 Math
lib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [Den
selyOrdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs 
: s in 𝓝[>=] a) (hfs : closure (f '' s) in 𝓝[>=] f a) : ContinuousWithinAt f (Ic
i a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[>=] a；hfs : closure (f '' s) in 𝓝[>=] f
 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin`：
continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyO
rdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : Monoton…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b

--- 原说明 ---
If a function `f` with a densely ordered codomain is strictly monotone on a righ
t neighborhood
of `a` and the closure of the image of this neighborhood under `f` is a right ne
ighborhood of `f a`,
then `f` is continuous at `a` from the right.
-/
theorem StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : closure (f '' s) ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
    (fun _ hx _ hy => (h_mono.le_iff_le hx hy).2) hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is
continuous at `a` from the right. -/
/-
**StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin [DenselyOrde
red β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝
[>=] a) (hfs : f '' s in 𝓝[>=] f a) : ContinuousWithinAt f (Ici a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[>=] a；hfs : f '' s in 𝓝[>=] f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin`：S
trictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrd
ered β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMo…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If a function `f` with a densely ordered codomain is strictly monotone on a righ
t neighborhood
of `a` and the image of this neighborhood under `f` is a right neighborhood of `
f a`, then `f` is
continuous at `a` from the right.
-/
theorem StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : f '' s ∈ 𝓝[≥] f a) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs
    (mem_of_superset hfs subset_closure)

/-- If a function `f` is strictly monotone on a right neighborhood of `a` and the image of this
neighborhood under `f` includes `Ioi (f a)`, then `f` is continuous at `a` from the right. -/
/-
**StrictMonoOn.continuousWithinAt_right_of_surjOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_right_of_surjOn {f : α -> β} {s : Set α} {
a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hfs : SurjOn f s (Ioi (f
 a))) : ContinuousWithinAt f (Ici a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[>=] a；hfs : SurjOn f s (Ioi (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_exists_between`：StrictMonoOn.co
ntinuousWithinAt_right_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_mon
o : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hf…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
If a function `f` is strictly monotone on a right neighborhood of `a` and the im
age of this
neighborhood under `f` includes `Ioi (f a)`, then `f` is continuous at `a` from 
the right.
-/
theorem StrictMonoOn.continuousWithinAt_right_of_surjOn {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : SurjOn f s (Ioi (f a))) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_exists_between hs fun _ hb =>
    let ⟨c, hcs, hcb⟩ := hfs hb
    ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

/-- If `f` is a strictly monotone function on a left neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, then `f` is continuous at `a`
from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x < 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
/-
**StrictMonoOn.continuousWithinAt_left_of_exists_between** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_left_of_exists_between {f : α -> β} {s : S
et α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[<=] a) (hfs : forall b < 
f a, exists c in s, f c in Ico b (f a)) : ContinuousWithinAt f (Iic a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[<=] a；hfs : forall b < f a, exists c in
 s, f c in Ico b (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_exists_between`：StrictMonoOn.co
ntinuousWithinAt_right_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_mon
o : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hf…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `StrictMonoOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictMonoOn (⇑Or
derDual…

--- 原说明 ---
If `f` is a strictly monotone function on a left neighborhood of `a` and the ima
ge of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, then `f` is c
ontinuous at `a`
from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` is required because
 otherwise the
function `f : ℝ → ℝ` given by `f x = if x < 0 then x else x + 1` would be a coun
ter-example at
`a = 0`.
-/
theorem StrictMonoOn.continuousWithinAt_left_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_exists_between hs fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

/-- If `f` is a monotone function on a left neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(b, f a)`, `b < f a`, then `f` is continuous at `a` from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)` cannot be replaced by the weaker
assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` we use for strictly monotone functions
because otherwise the function `floor : ℝ → ℤ` would be a counter-example at `a = 0`. -/
/-
**continuousWithinAt_left_of_monotoneOn_of_exists_between** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：continuousWithinAt_left_of_monotoneOn_of_exists_between {f : α -> β} {s : 
Set α} {a : α} (hf : MonotoneOn f s) (hs : s in 𝓝[<=] a) (hfs : forall b < f a, 
exists c in s, f c in Ioo b (f a)) : ContinuousWithinAt f (Iic a) a
参数：hf : MonotoneOn f s；hs : s in 𝓝[<=] a；hfs : forall b < f a, exists c in s, f 
c in Ioo b (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_exists_between`：continuousWith
inAt_right_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_m
ono : MonotoneOn f s) (hs : s in 𝓝[>=] a) (hfs…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…

--- 原说明 ---
If `f` is a monotone function on a left neighborhood of `a` and the image of thi
s neighborhood
under `f` meets every interval `(b, f a)`, `b < f a`, then `f` is continuous at 
`a` from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)` cannot be replaced 
by the weaker
assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` we use for strictly mon
otone functions
because otherwise the function `floor : ℝ → ℤ` would be a counter-example at `a 
= 0`.
-/
theorem continuousWithinAt_left_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (hf : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_exists_between αᵒᵈ βᵒᵈ _ _ _ _ _ _ f s a hf.dual hs
    fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left -/
/-
**continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin** 是 Math
lib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [Den
selyOrdered β] {f : α -> β} {s : Set α} {a : α} (hf : MonotoneOn f s) (hs : s in
 𝓝[<=] a) (hfs : closure (f '' s) in 𝓝[<=] f a) : ContinuousWithinAt f (Iic a) a
参数：hf : MonotoneOn f s；hs : s in 𝓝[<=] a；hfs : closure (f '' s) in 𝓝[<=] f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin`：
continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyO
rdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : Monoton…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…

--- 原说明 ---
If a function `f` with a densely ordered codomain is monotone on a left neighbor
hood of `a` and
the closure of the image of this neighborhood under `f` is a left neighborhood o
f `f a`, then `f` is
continuous at `a` from the left
-/
theorem continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (hf : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a)
    (hfs : closure (f '' s) ∈ 𝓝[≤] f a) : ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ f s
    a hf.dual hs hfs

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is continuous at
`a` from the left. -/
/-
**continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrde
red β] {f : α -> β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝[<
=] a) (hfs : f '' s in 𝓝[<=] f a) : ContinuousWithinAt f (Iic a) a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝[<=] a；hfs : f '' s in 𝓝[<=] f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin`：c
ontinuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrd
ered β] {f : α -> β} {s : Set α} {a : α} (hf : MonotoneOn f…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If a function `f` with a densely ordered codomain is monotone on a left neighbor
hood of `a` and
the image of this neighborhood under `f` is a left neighborhood of `f a`, then `
f` is continuous at
`a` from the left.
-/
theorem continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : f '' s ∈ 𝓝[≤] f a) :
    ContinuousWithinAt f (Iic a) a :=
  continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    (mem_of_superset hfs subset_closure)

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`,
then `f` is continuous at `a` from the left. -/
/-
**StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin** 是 Mathl
ib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin [Dens
elyOrdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs :
 s in 𝓝[<=] a) (hfs : closure (f '' s) in 𝓝[<=] f a) : ContinuousWithinAt f (Iic
 a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[<=] a；hfs : closure (f '' s) in 𝓝[<=] f
 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin`：S
trictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrd
ered β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMo…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `StrictMonoOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictMonoOn (⇑Or
derDual…

--- 原说明 ---
If a function `f` with a densely ordered codomain is strictly monotone on a left
 neighborhood of
`a` and the closure of the image of this neighborhood under `f` is a left neighb
orhood of `f a`,
then `f` is continuous at `a` from the left.
-/
theorem StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a)
    (hfs : closure (f '' s) ∈ 𝓝[≤] f a) : ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left. -/
/-
**StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin [DenselyOrder
ed β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[
<=] a) (hfs : f '' s in 𝓝[<=] f a) : ContinuousWithinAt f (Iic a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[<=] a；hfs : f '' s in 𝓝[<=] f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin`：StrictMon
oOn.continuousWithinAt_right_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α -
> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `StrictMonoOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictMonoOn (⇑Or
derDual…

--- 原说明 ---
If a function `f` with a densely ordered codomain is strictly monotone on a left
 neighborhood of
`a` and the image of this neighborhood under `f` is a left neighborhood of `f a`
, then `f` is
continuous at `a` from the left.
-/
theorem StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : f '' s ∈ 𝓝[≤] f a) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin hs hfs

/-- If a function `f` is strictly monotone on a left neighborhood of `a` and the image of this
neighborhood under `f` includes `Iio (f a)`, then `f` is continuous at `a` from the left. -/
/-
**StrictMonoOn.continuousWithinAt_left_of_surjOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousWithinAt_left_of_surjOn {f : α -> β} {s : Set α} {a
 : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[<=] a) (hfs : SurjOn f s (Iio (f 
a))) : ContinuousWithinAt f (Iic a) a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝[<=] a；hfs : SurjOn f s (Iio (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_surjOn`：StrictMonoOn.continuous
WithinAt_right_of_surjOn {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn
 f s) (hs : s in 𝓝[>=] a) (hfs : Surj…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `StrictMonoOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictMonoOn (⇑Or
derDual…

--- 原说明 ---
If a function `f` is strictly monotone on a left neighborhood of `a` and the ima
ge of this
neighborhood under `f` includes `Iio (f a)`, then `f` is continuous at `a` from 
the left.
-/
theorem StrictMonoOn.continuousWithinAt_left_of_surjOn {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : SurjOn f s (Iio (f a))) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_surjOn hs hfs

/-- If a function `f` is strictly monotone on a neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, and every interval
`(f a, b]`, `b > f a`, then `f` is continuous at `a`. -/
/-
**StrictMonoOn.continuousAt_of_exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousAt_of_exists_between {f : α -> β} {s : Set α} {a : 
α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝 a) (hfs_l : forall b < f a, exists c
 in s, f c in Ico b (f a)) (hfs_r : forall b > f a, exists c in s, f c in Ioc (f
 a) b) : ContinuousAt f a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝 a；hfs_l : forall b < f a, exists c in s
, f c in Ico b (f a)；hfs_r : forall b > f a, exists c in s, f c in Ioc (f a) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_iff_continuous_left_right`：continuousAt_iff_continuous_left
_right {a : α} {f : α -> β} : ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a 
∧ ContinuousWithinAt f (Ici …
· 使用定理 `StrictMonoOn.continuousWithinAt_left_of_exists_between`：StrictMonoOn.con
tinuousWithinAt_left_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_mono 
: StrictMonoOn f s) (hs : s in 𝓝[<=] a) (hfs…
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_exists_between`：StrictMonoOn.co
ntinuousWithinAt_right_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_mon
o : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hf…

--- 原说明 ---
If a function `f` is strictly monotone on a neighborhood of `a` and the image of
 this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, and every int
erval
`(f a, b]`, `b > f a`, then `f` is continuous at `a`.
-/
theorem StrictMonoOn.continuousAt_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a))
    (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_l,
      h_mono.continuousWithinAt_right_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
/-
**StrictMonoOn.continuousAt_of_closure_image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：StrictMonoOn.continuousAt_of_closure_image_mem_nhds [DenselyOrdered β] {f 
: α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝 a) (hfs :
 closure (f '' s) in 𝓝 (f a)) : ContinuousAt f a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝 a；hfs : closure (f '' s) in 𝓝 (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_iff_continuous_left_right`：continuousAt_iff_continuous_left
_right {a : α} {f : α -> β} : ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a 
∧ ContinuousWithinAt f (Ici …
· 使用定理 `StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin`：St
rictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin [DenselyOrder
ed β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMon…
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin`：S
trictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrd
ered β] {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMo…

--- 原说明 ---
If a function `f` with a densely ordered codomain is strictly monotone on a neig
hborhood of `a`
and the closure of the image of this neighborhood under `f` is a neighborhood of
 `f a`, then `f` is
continuous at `a`.
-/
theorem StrictMonoOn.continuousAt_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a)
    (hfs : closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hs)
        (mem_nhdsWithin_of_mem_nhds hfs),
      h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the image of this set under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
/-
**StrictMonoOn.continuousAt_of_image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.continuousAt_of_image_mem_nhds [DenselyOrdered β] {f : α -> β
} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝 a) (hfs : f '' s 
in 𝓝 (f a)) : ContinuousAt f a
参数：h_mono : StrictMonoOn f s；hs : s in 𝓝 a；hfs : f '' s in 𝓝 (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.continuousAt_of_closure_image_mem_nhds`：StrictMonoOn.contin
uousAt_of_closure_image_mem_nhds [DenselyOrdered β] {f : α -> β} {s : Set α} {a 
: α} (h_mono : StrictMonoOn f s) (hs : s …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If a function `f` with a densely ordered codomain is strictly monotone on a neig
hborhood of `a`
and the image of this set under `f` is a neighborhood of `f a`, then `f` is cont
inuous at `a`.
-/
theorem StrictMonoOn.continuousAt_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α}
    {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) :
    ContinuousAt f a :=
  h_mono.continuousAt_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

/-- If `f` is a monotone function on a neighborhood of `a` and the image of this neighborhood under
`f` meets every interval `(b, f a)`, `b < f a`, and every interval `(f a, b)`, `b > f a`, then `f`
is continuous at `a`. -/
/-
**continuousAt_of_monotoneOn_of_exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a :
 α} (h_mono : MonotoneOn f s) (hs : s in 𝓝 a) (hfs_l : forall b < f a, exists c 
in s, f c in Ioo b (f a)) (hfs_r : forall b > f a, exists c in s, f c in Ioo (f 
a) b) : ContinuousAt f a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝 a；hfs_l : forall b < f a, exists c in s, 
f c in Ioo b (f a)；hfs_r : forall b > f a, exists c in s, f c in Ioo (f a) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_iff_continuous_left_right`：continuousAt_iff_continuous_left
_right {a : α} {f : α -> β} : ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a 
∧ ContinuousWithinAt f (Ici …
· 使用定理 `continuousWithinAt_left_of_monotoneOn_of_exists_between`：continuousWithi
nAt_left_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α} (hf : 
MonotoneOn f s) (hs : s in 𝓝[<=] a) (hfs : fo…
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_exists_between`：continuousWith
inAt_right_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α} (h_m
ono : MonotoneOn f s) (hs : s in 𝓝[>=] a) (hfs…

--- 原说明 ---
If `f` is a monotone function on a neighborhood of `a` and the image of this nei
ghborhood under
`f` meets every interval `(b, f a)`, `b < f a`, and every interval `(f a, b)`, `
b > f a`, then `f`
is continuous at `a`.
-/
theorem continuousAt_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a))
    (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_exists_between h_mono (mem_nhdsWithin_of_mem_nhds hs)
        hfs_l,
      continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono
        (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
/-
**continuousAt_of_monotoneOn_of_closure_image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：continuousAt_of_monotoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f
 : α -> β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝 a) (hfs : 
closure (f '' s) in 𝓝 (f a)) : ContinuousAt f a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝 a；hfs : closure (f '' s) in 𝓝 (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_iff_continuous_left_right`：continuousAt_iff_continuous_left
_right {a : α} {f : α -> β} : ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a 
∧ ContinuousWithinAt f (Ici …
· 使用定理 `continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin`：c
ontinuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrd
ered β] {f : α -> β} {s : Set α} {a : α} (hf : MonotoneOn f…
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin`：
continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyO
rdered β] {f : α -> β} {s : Set α} {a : α} (h_mono : Monoton…

--- 原说明 ---
If a function `f` with a densely ordered codomain is monotone on a neighborhood 
of `a` and the
closure of the image of this neighborhood under `f` is a neighborhood of `f a`, 
then `f` is
continuous at `a`.
-/
theorem continuousAt_of_monotoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a)
    (hfs : closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs),
      continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
/-
**continuousAt_of_monotoneOn_of_image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_of_monotoneOn_of_image_mem_nhds [DenselyOrdered β] {f : α -> 
β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝 a) (hfs : f '' s i
n 𝓝 (f a)) : ContinuousAt f a
参数：h_mono : MonotoneOn f s；hs : s in 𝓝 a；hfs : f '' s in 𝓝 (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_of_monotoneOn_of_closure_image_mem_nhds`：continuousAt_of_mo
notoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f : α -> β} {s : Set α} {
a : α} (h_mono : MonotoneOn f s) (hs : s i…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If a function `f` with a densely ordered codomain is monotone on a neighborhood 
of `a` and the
image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is con
tinuous at `a`.
-/
theorem continuousAt_of_monotoneOn_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α}
    {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_of_monotoneOn_of_closure_image_mem_nhds h_mono hs
    (mem_of_superset hfs subset_closure)

/-- A monotone function with densely ordered codomain and a dense range is continuous. -/
/-
**Monotone.continuous_of_denseRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.continuous_of_denseRange [DenselyOrdered β] {f : α -> β} (h_mono 
: Monotone f) (h_dense : DenseRange f) : Continuous f
参数：h_mono : Monotone f；h_dense : DenseRange f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_of_monotoneOn_of_closure_image_mem_nhds`：continuousAt_of_mo
notoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f : α -> β} {s : Set α} {
a : α} (h_mono : MonotoneOn f s) (hs : s i…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ

--- 原说明 ---
A monotone function with densely ordered codomain and a dense range is continuou
s.
-/
theorem Monotone.continuous_of_denseRange [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
    (h_dense : DenseRange f) : Continuous f :=
  continuous_iff_continuousAt.mpr fun a =>
    continuousAt_of_monotoneOn_of_closure_image_mem_nhds (fun _ _ _ _ hxy => h_mono hxy)
        univ_mem <|
      by simp only [image_univ, h_dense.closure_eq, univ_mem]

/-- A monotone surjective function with a densely ordered codomain is continuous. -/
/-
**Monotone.continuous_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.continuous_of_surjective [DenselyOrdered β] {f : α -> β} (h_mono 
: Monotone f) (h_surj : Function.Surjective f) : Continuous f
参数：h_mono : Monotone f；h_surj : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.continuous_of_denseRange`：Monotone.continuous_of_denseRange [De
nselyOrdered β] {f : α -> β} (h_mono : Monotone f) (h_dense : DenseRange f) : Co
ntinuous f
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f

--- 原说明 ---
A monotone surjective function with a densely ordered codomain is continuous.
-/
theorem Monotone.continuous_of_surjective [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
    (h_surj : Function.Surjective f) : Continuous f :=
  h_mono.continuous_of_denseRange h_surj.denseRange

end LinearOrder

/-!
### Continuity of order isomorphisms

In this section we prove that an `OrderIso` is continuous, hence it is a `Homeomorph`. We prove
this for an `OrderIso` between to partial orders with order topology.
-/


namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [OrderTopology α] [OrderTopology β]

/-
**OrderIso.continuous** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpace β] [OrderTopology α] 
[OrderTopology β] (e : α ≃o β), Continuous ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderTopology.topology_eq_generate_intervals`：∀ {α : Type u_1} {t : Topo
logicalSpace α} {inst : Preorder α} [self : OrderTopology α], t = Preorder.topol
ogy α
· 使用引理 `continuous_generateFrom_iff`：continuous_generateFrom_iff {t : Topologica
lSpace α} {b : Set (Set β)} : Continuous[t, generateFrom b] f ↔ forall s in b, I
sOpen (f ⁻¹' s)
· 使用定理 `OrderIso.preimage_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder 
α] [inst_1 : Preorder β] (e : α ≃o β) (b : β),   ⇑e ⁻¹' Set.Ioi b = Set.Ioi (e.s
ymm b)
· 使用定理 `isOpen_lt'`：isOpen_lt' [OrderTopology α] (a : α) : IsOpen { b : α | a < 
b }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.preimage_Iio`：preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b =
 Iio (e.symm b)
· 使用定理 `isOpen_gt'`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α]
 [OrderTopology α] (a : α), IsOpen {b | b < a}
-/
protected theorem continuous (e : α ≃o β) : Continuous e := by
  rw [‹OrderTopology β›.topology_eq_generate_intervals, continuous_generateFrom_iff]
  rintro s ⟨a, rfl | rfl⟩
  · rw [e.preimage_Ioi]
    apply isOpen_lt'
  · rw [e.preimage_Iio]
    apply isOpen_gt'
/-
**OrderIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomeomorphClass (α ≃o β) α β where
  map_continuous := OrderIso.continuous
  inv_continuous e := e.symm.continuous

/-- An order isomorphism between two linear order `OrderTopology` spaces is a homeomorphism. -/
/-
**OrderIso.toHomeomorph** 是 Mathlib 中的一个缩写定义，位于命名空间 `OrderIso`。
形式化陈述：toHomeomorph (e : α ≃o β) : α ≃ₜ β
参数：e : α ≃o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.instHomeomorphClass`：∀ {α : Type u_1} {β : Type u_2} [inst : Pr
eorder α] [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : Topolo
gicalSpace β] [Ord…

--- 原说明 ---
An order isomorphism between two linear order `OrderTopology` spaces is a homeom
orphism.
-/
abbrev toHomeomorph (e : α ≃o β) : α ≃ₜ β :=
  HomeomorphClass.toHomeomorph e
/-
**OrderIso.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_toHomeomorph (e : α ≃o β) : ⇑e.toHomeomorph = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph (e : α ≃o β) : ⇑e.toHomeomorph = e :=
  rfl --Simp can prove this too

@[simp]
/-
**OrderIso.coe_toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_toHomeomorph_symm (e : α ≃o β) : ⇑e.toHomeomorph.symm = e.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph_symm (e : α ≃o β) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

end OrderIso

