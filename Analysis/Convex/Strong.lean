/-
Copyright (c) 2023 Yaël Dillies, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Uniformly and strongly convex functions

In this file, we define uniformly convex functions and strongly convex functions.

For a real normed space `E`, a uniformly convex function with modulus `φ : ℝ → ℝ` is a function
`f : E → ℝ` such that `f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖`
for all `t ∈ [0, 1]`.

A `m`-strongly convex function is a uniformly convex function with modulus `fun r ↦ m / 2 * r ^ 2`.
If `E` is an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex.

## TODO

Prove derivative properties of strongly convex functions.
-/

@[expose] public section

open Real

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace
variable [NormedSpace Real E] {φ ψ : Real -> Real} {s : Set E} {m : Real} {f g : E -> Real}

/--
Definition of `UniformConvexOn` / `UniformConvexOn` 的定义

English:
definition UniformConvexOn
  signature: (s : Set E) (φ : Real -> Real) (f : E -> Real)
  body: Convex Real s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : Real⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    f (a • x + b • y) <= a • f x + b • f y - a * b * φ ‖x - y‖

中文:
定义 UniformConvexOn
  签名: (s : Set E) (φ : 实数 -> 实数) (f : E -> 实数)
  定义体: Convex Real s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : Real⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    f (a • x + b • y) <= a • f x + b • f y - a * b * φ ‖x - y‖

Depends on / 依赖: Convex
-/
def UniformConvexOn (s : Set E) (φ : Real -> Real) (f : E -> Real) : Prop :=
  Convex Real s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : Real⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    f (a • x + b • y) <= a • f x + b • f y - a * b * φ ‖x - y‖

/--
Definition of `UniformConcaveOn` / `UniformConcaveOn` 的定义

English:
definition UniformConcaveOn
  signature: (s : Set E) (φ : Real -> Real) (f : E -> Real)
  body: Convex Real s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : Real⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • f x + b • f y + a * b * φ ‖x - y‖ <= f (a • x + b • y)

中文:
定义 UniformConcaveOn
  签名: (s : Set E) (φ : 实数 -> 实数) (f : E -> 实数)
  定义体: Convex Real s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : Real⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • f x + b • f y + a * b * φ ‖x - y‖ <= f (a • x + b • y)

Depends on / 依赖: Convex
-/
def UniformConcaveOn (s : Set E) (φ : Real -> Real) (f : E -> Real) : Prop :=
  Convex Real s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : Real⦄, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • f x + b • f y + a * b * φ ‖x - y‖ <= f (a • x + b • y)

/--
lemma `uniformConvexOn_zero` / 引理 `uniformConvexOn_zero`

English:
lemma uniformConvexOn_zero
  statement: UniformConvexOn s 0 f ↔ ConvexOn Real s f
  proof: by
  simp [UniformConvexOn, ConvexOn]

中文:
引理 uniformConvexOn_zero
  结论: UniformConvexOn s 0 f ↔ ConvexOn 实数 s f
  证明: by
  simp [UniformConvexOn, ConvexOn]
-/
@[simp] lemma uniformConvexOn_zero : UniformConvexOn s 0 f ↔ ConvexOn Real s f := by
  simp [UniformConvexOn, ConvexOn]

/--
lemma `uniformConcaveOn_zero` / 引理 `uniformConcaveOn_zero`

English:
lemma uniformConcaveOn_zero
  statement: UniformConcaveOn s 0 f ↔ ConcaveOn Real s f
  proof: by
  simp [UniformConcaveOn, ConcaveOn]

protected alias ⟨_, ConvexOn.uniformConvexOn_zero⟩ := uniformConvexOn_zero
protected alias ⟨_, ConcaveOn.uniformConcaveOn_zero⟩ := uniformConcaveOn_zero

中文:
引理 uniformConcaveOn_zero
  结论: UniformConcaveOn s 0 f ↔ ConcaveOn 实数 s f
  证明: by
  simp [UniformConcaveOn, ConcaveOn]

protected alias ⟨_, ConvexOn.uniformConvexOn_zero⟩ := uniformConvexOn_zero
protected alias ⟨_, ConcaveOn.uniformConcaveOn_zero⟩ := uniformConcaveOn_zero
-/
@[simp] lemma uniformConcaveOn_zero : UniformConcaveOn s 0 f ↔ ConcaveOn Real s f := by
  simp [UniformConcaveOn, ConcaveOn]

protected alias ⟨_, ConvexOn.uniformConvexOn_zero⟩ := uniformConvexOn_zero
protected alias ⟨_, ConcaveOn.uniformConcaveOn_zero⟩ := uniformConcaveOn_zero

/--
lemma `UniformConvexOn.mono` / 引理 `UniformConvexOn.mono`

English:
lemma UniformConvexOn.mono
  given: (hψφ : ψ <= φ) (hf : UniformConvexOn s φ f)
  statement: UniformConvexOn s ψ f
  proof: ⟨hf.1, fun x hx y hy a b ha hb hab => (hf.2 hx hy ha hb hab).trans by gcongr; apply hψφ⟩

中文:
引理 UniformConvexOn.mono
  条件: (hψφ : ψ <= φ) (hf : UniformConvexOn s φ f)
  结论: UniformConvexOn s ψ f
  证明: ⟨hf.1, fun x hx y hy a b ha hb hab => (hf.2 hx hy ha hb hab).trans by gcongr; apply hψφ⟩
-/
lemma UniformConvexOn.mono (hψφ : ψ <= φ) (hf : UniformConvexOn s φ f) : UniformConvexOn s ψ f :=
⟨hf.1, fun x hx y hy a b ha hb hab => (hf.2 hx hy ha hb hab).trans by gcongr; apply hψφ⟩

/--
lemma `UniformConcaveOn.mono` / 引理 `UniformConcaveOn.mono`

English:
lemma UniformConcaveOn.mono
  given: (hψφ : ψ <= φ) (hf : UniformConcaveOn s φ f)
  statement: UniformConcaveOn s ψ f
  proof: ⟨hf.1, fun x hx y hy a b ha hb hab => (hf.2 hx hy ha hb hab).trans' by gcongr; apply hψφ⟩

中文:
引理 UniformConcaveOn.mono
  条件: (hψφ : ψ <= φ) (hf : UniformConcaveOn s φ f)
  结论: UniformConcaveOn s ψ f
  证明: ⟨hf.1, fun x hx y hy a b ha hb hab => (hf.2 hx hy ha hb hab).trans' by gcongr; apply hψφ⟩
-/
lemma UniformConcaveOn.mono (hψφ : ψ <= φ) (hf : UniformConcaveOn s φ f) : UniformConcaveOn s ψ f :=
⟨hf.1, fun x hx y hy a b ha hb hab => (hf.2 hx hy ha hb hab).trans' by gcongr; apply hψφ⟩

/--
lemma `UniformConvexOn.convexOn` / 引理 `UniformConvexOn.convexOn`

English:
lemma UniformConvexOn.convexOn
  given: (hf : UniformConvexOn s φ f) (hφ : 0 <= φ)
  statement: ConvexOn Real s f
  proof: by
  simpa using hf.mono hφ

中文:
引理 UniformConvexOn.convexOn
  条件: (hf : UniformConvexOn s φ f) (hφ : 0 <= φ)
  结论: ConvexOn 实数 s f
  证明: by
  simpa using hf.mono hφ

Depends on / 依赖: hf.mono
-/
lemma UniformConvexOn.convexOn (hf : UniformConvexOn s φ f) (hφ : 0 <= φ) : ConvexOn Real s f := by
  simpa using hf.mono hφ

/--
lemma `UniformConcaveOn.concaveOn` / 引理 `UniformConcaveOn.concaveOn`

English:
lemma UniformConcaveOn.concaveOn
  given: (hf : UniformConcaveOn s φ f) (hφ : 0 <= φ)
  statement: ConcaveOn Real s f
  proof: by
  simpa using hf.mono hφ

中文:
引理 UniformConcaveOn.concaveOn
  条件: (hf : UniformConcaveOn s φ f) (hφ : 0 <= φ)
  结论: ConcaveOn 实数 s f
  证明: by
  simpa using hf.mono hφ

Depends on / 依赖: hf.mono
-/
lemma UniformConcaveOn.concaveOn (hf : UniformConcaveOn s φ f) (hφ : 0 <= φ) : ConcaveOn Real s f := by
  simpa using hf.mono hφ

/--
lemma `UniformConvexOn.strictConvexOn` / 引理 `UniformConvexOn.strictConvexOn`

English:
lemma UniformConvexOn.strictConvexOn
  given: (hf : UniformConvexOn s φ f) (hφ : forall r, r != 0 -> 0 < φ r)
  proof: by
refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy ha.le hb.le hab).trans_lt
    sub_lt_self _ ?_⟩
  rw [← sub_ne_zero]; rw [← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

中文:
引理 UniformConvexOn.strictConvexOn
  条件: (hf : UniformConvexOn s φ f) (hφ : 对任意 r, r != 0 -> 0 < φ r)
  证明: by
refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy ha.le hb.le hab).trans_lt
    sub_lt_self _ ?_⟩
  rw [← sub_ne_zero]; rw [← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

Depends on / 依赖: ha.le, hb.le, hxy.ne, norm_pos_iff, sub_lt_self, sub_ne_zero, trans_lt
-/
lemma UniformConvexOn.strictConvexOn (hf : UniformConvexOn s φ f) (hφ : forall r, r != 0 -> 0 < φ r) :
    StrictConvexOn Real s f := by
refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy ha.le hb.le hab).trans_lt
    sub_lt_self _ ?_⟩
  rw [← sub_ne_zero]; rw [← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

/--
lemma `UniformConcaveOn.strictConcaveOn` / 引理 `UniformConcaveOn.strictConcaveOn`

English:
lemma UniformConcaveOn.strictConcaveOn
  given: (hf : UniformConcaveOn s φ f) (hφ : forall r, r != 0 -> 0 < φ r)
  proof: by
refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy ha.le hb.le hab).trans_lt'
    lt_add_of_pos_right _ ?_⟩
  rw [← sub_ne_zero]; rw [← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

中文:
引理 UniformConcaveOn.strictConcaveOn
  条件: (hf : UniformConcaveOn s φ f) (hφ : 对任意 r, r != 0 -> 0 < φ r)
  证明: by
refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy ha.le hb.le hab).trans_lt'
    lt_add_of_pos_right _ ?_⟩
  rw [← sub_ne_zero]; rw [← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

Depends on / 依赖: ha.le, hb.le, hxy.ne, lt_add_of_pos_right, norm_pos_iff, sub_ne_zero, trans_lt
-/
lemma UniformConcaveOn.strictConcaveOn (hf : UniformConcaveOn s φ f) (hφ : forall r, r != 0 -> 0 < φ r) :
    StrictConcaveOn Real s f := by
refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy ha.le hb.le hab).trans_lt'
    lt_add_of_pos_right _ ?_⟩
  rw [← sub_ne_zero]; rw [← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

/--
lemma `UniformConvexOn.add` / 引理 `UniformConvexOn.add`

English:
lemma UniformConvexOn.add
  given: (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g)
  proof: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

中文:
引理 UniformConvexOn.add
  条件: (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g)
  证明: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

Depends on / 依赖: add_add_add_comm, add_le_add, mul_add, sub_add_sub_comm
-/
lemma UniformConvexOn.add (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

/--
lemma `UniformConcaveOn.add` / 引理 `UniformConcaveOn.add`

English:
lemma UniformConcaveOn.add
  given: (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g)
  proof: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

中文:
引理 UniformConcaveOn.add
  条件: (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g)
  证明: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

Depends on / 依赖: add_add_add_comm, add_le_add, mul_add
-/
lemma UniformConcaveOn.add (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

/--
lemma `UniformConvexOn.neg` / 引理 `UniformConvexOn.neg`

English:
lemma UniformConvexOn.neg
  given: (hf : UniformConvexOn s φ f)
  statement: UniformConcaveOn s φ (-f)
  proof: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, le_sub_iff_add_le'] using hf.2 hx hy ha hb hab

中文:
引理 UniformConvexOn.neg
  条件: (hf : UniformConvexOn s φ f)
  结论: UniformConcaveOn s φ (-f)
  证明: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, le_sub_iff_add_le'] using hf.2 hx hy ha hb hab

Depends on / 依赖: add_comm, le_of_neg_le_neg, le_sub_iff_add_le, neg_le_neg_iff
-/
lemma UniformConvexOn.neg (hf : UniformConvexOn s φ f) : UniformConcaveOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, le_sub_iff_add_le'] using hf.2 hx hy ha hb hab

/--
lemma `UniformConcaveOn.neg` / 引理 `UniformConcaveOn.neg`

English:
lemma UniformConcaveOn.neg
  given: (hf : UniformConcaveOn s φ f)
  statement: UniformConvexOn s φ (-f)
  proof: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, ← le_sub_iff_add_le', sub_eq_add_neg, neg_add]
    using hf.2 hx hy ha hb hab

中文:
引理 UniformConcaveOn.neg
  条件: (hf : UniformConcaveOn s φ f)
  结论: UniformConvexOn s φ (-f)
  证明: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, ← le_sub_iff_add_le', sub_eq_add_neg, neg_add]
    using hf.2 hx hy ha hb hab

Depends on / 依赖: add_comm, le_of_neg_le_neg, le_sub_iff_add_le, neg_add, neg_le_neg_iff, sub_eq_add_neg
-/
lemma UniformConcaveOn.neg (hf : UniformConcaveOn s φ f) : UniformConvexOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, ← le_sub_iff_add_le', sub_eq_add_neg, neg_add]
    using hf.2 hx hy ha hb hab

/--
lemma `UniformConvexOn.sub` / 引理 `UniformConvexOn.sub`

English:
lemma UniformConvexOn.sub
  given: (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g)
  proof: by simpa using! hf.add hg.neg

中文:
引理 UniformConvexOn.sub
  条件: (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g)
  证明: by simpa using! hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg
-/
lemma UniformConvexOn.sub (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f - g) := by simpa using! hf.add hg.neg

/--
lemma `UniformConcaveOn.sub` / 引理 `UniformConcaveOn.sub`

English:
lemma UniformConcaveOn.sub
  given: (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g)
  proof: by simpa using! hf.add hg.neg

中文:
引理 UniformConcaveOn.sub
  条件: (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g)
  证明: by simpa using! hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg
-/
lemma UniformConcaveOn.sub (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by simpa using! hf.add hg.neg

/--
Definition of `StrongConvexOn` / `StrongConvexOn` 的定义

English:
definition StrongConvexOn
  signature: (s : Set E) (m : Real)
  body: UniformConvexOn s fun r => m / (2 : Real) * r ^ 2

中文:
定义 StrongConvexOn
  签名: (s : Set E) (m : 实数)
  定义体: UniformConvexOn s fun r => m / (2 : Real) * r ^ 2

Depends on / 依赖: UniformConvexOn
-/
def StrongConvexOn (s : Set E) (m : Real) : (E -> Real) -> Prop :=
  UniformConvexOn s fun r => m / (2 : Real) * r ^ 2

/--
Definition of `StrongConcaveOn` / `StrongConcaveOn` 的定义

English:
definition StrongConcaveOn
  signature: (s : Set E) (m : Real)
  body: UniformConcaveOn s fun r => m / (2 : Real) * r ^ 2

中文:
定义 StrongConcaveOn
  签名: (s : Set E) (m : 实数)
  定义体: UniformConcaveOn s fun r => m / (2 : Real) * r ^ 2

Depends on / 依赖: UniformConcaveOn
-/
def StrongConcaveOn (s : Set E) (m : Real) : (E -> Real) -> Prop :=
  UniformConcaveOn s fun r => m / (2 : Real) * r ^ 2

variable {s : Set E} {f : E -> Real} {m n : Real}

nonrec lemma StrongConvexOn.mono (hmn : m <= n) (hf : StrongConvexOn s n f) : StrongConvexOn s m f :=
  hf.mono fun r => by gcongr

nonrec lemma StrongConcaveOn.mono (hmn : m <= n) (hf : StrongConcaveOn s n f) :
    StrongConcaveOn s m f := hf.mono fun r => by gcongr

/--
lemma `strongConvexOn_zero` / 引理 `strongConvexOn_zero`

English:
lemma strongConvexOn_zero
  statement: StrongConvexOn s 0 f ↔ ConvexOn Real s f
  proof: by
  simp [StrongConvexOn, ← Pi.zero_def]

中文:
引理 strongConvexOn_zero
  结论: StrongConvexOn s 0 f ↔ ConvexOn 实数 s f
  证明: by
  simp [StrongConvexOn, ← Pi.zero_def]
-/
@[simp] lemma strongConvexOn_zero : StrongConvexOn s 0 f ↔ ConvexOn Real s f := by
  simp [StrongConvexOn, ← Pi.zero_def]

/--
lemma `strongConcaveOn_zero` / 引理 `strongConcaveOn_zero`

English:
lemma strongConcaveOn_zero
  statement: StrongConcaveOn s 0 f ↔ ConcaveOn Real s f
  proof: by
  simp [StrongConcaveOn, ← Pi.zero_def]

nonrec lemma StrongConvexOn.strictConvexOn (hf : StrongConvexOn s m f) (hm : 0 < m) :
    StrictConvexOn Real s f := hf.strictConvexOn fun r hr => by positivity

nonrec lemma StrongConcaveOn.strictConcaveOn (hf : StrongConcaveOn s m f) (hm : 0 < m) :
    S

中文:
引理 strongConcaveOn_zero
  结论: StrongConcaveOn s 0 f ↔ ConcaveOn 实数 s f
  证明: by
  simp [StrongConcaveOn, ← Pi.zero_def]

nonrec lemma StrongConvexOn.strictConvexOn (hf : StrongConvexOn s m f) (hm : 0 < m) :
    StrictConvexOn Real s f := hf.strictConvexOn fun r hr => by positivity

nonrec lemma StrongConcaveOn.strictConcaveOn (hf : StrongConcaveOn s m f) (hm : 0 < m) :
    S
-/
@[simp] lemma strongConcaveOn_zero : StrongConcaveOn s 0 f ↔ ConcaveOn Real s f := by
  simp [StrongConcaveOn, ← Pi.zero_def]

nonrec lemma StrongConvexOn.strictConvexOn (hf : StrongConvexOn s m f) (hm : 0 < m) :
    StrictConvexOn Real s f := hf.strictConvexOn fun r hr => by positivity

nonrec lemma StrongConcaveOn.strictConcaveOn (hf : StrongConcaveOn s m f) (hm : 0 < m) :
    StrictConcaveOn Real s f := hf.strictConcaveOn fun r hr => by positivity

end NormedSpace

section InnerProductSpace
variable [InnerProductSpace Real E] {s : Set E} {a b m : Real} {x y : E} {f : E -> Real}

/--
lemma `aux_sub` / 引理 `aux_sub`

English:
lemma aux_sub
  given: (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  proof: by
  rw [norm_add_sq_real]; rw [norm_sub_sq_real]; rw [norm_smul]; rw [norm_smul]; rw [real_inner_smul_left]; rw [inner_smul_right]; rw [norm_of_nonneg ha]; rw [norm_of_nonneg hb]; rw [mul_pow]; rw [mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring_nf

中文:
引理 aux_sub
  条件: (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  证明: by
  rw [norm_add_sq_real]; rw [norm_sub_sq_real]; rw [norm_smul]; rw [norm_smul]; rw [real_inner_smul_left]; rw [inner_smul_right]; rw [norm_of_nonneg ha]; rw [norm_of_nonneg hb]; rw [mul_pow]; rw [mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring_nf
-/
private lemma aux_sub (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    a * (f x - m / (2 : Real) * ‖x‖ ^ 2) + b * (f y - m / (2 : Real) * ‖y‖ ^ 2) +
      m / (2 : Real) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y - m / (2 : Real) * a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real]; rw [norm_sub_sq_real]; rw [norm_smul]; rw [norm_smul]; rw [real_inner_smul_left]; rw [inner_smul_right]; rw [norm_of_nonneg ha]; rw [norm_of_nonneg hb]; rw [mul_pow]; rw [mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring_nf

/--
lemma `aux_add` / 引理 `aux_add`

English:
lemma aux_add
  given: (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  proof: by
  simpa [neg_div] using! aux_sub (E := E) (m := -m) ha hb hab

中文:
引理 aux_add
  条件: (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  证明: by
  simpa [neg_div] using! aux_sub (E := E) (m := -m) ha hb hab
-/
private lemma aux_add (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    a * (f x + m / (2 : Real) * ‖x‖ ^ 2) + b * (f y + m / (2 : Real) * ‖y‖ ^ 2) -
      m / (2 : Real) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y + m / (2 : Real) * a * b * ‖x - y‖ ^ 2 := by
  simpa [neg_div] using! aux_sub (E := E) (m := -m) ha hb hab

/--
lemma `strongConvexOn_iff_convex` / 引理 `strongConvexOn_iff_convex`

English:
lemma strongConvexOn_iff_convex
  proof: by
  refine and_congr_right fun _ => forall₄_congr fun x _ y _ => forall₅_congr fun a b ha hb hab => ?_
  simp_rw [sub_le_iff_le_add, smul_eq_mul, aux_sub ha hb hab, mul_assoc, mul_left_comm]

中文:
引理 strongConvexOn_iff_convex
  证明: by
  refine and_congr_right fun _ => forall₄_congr fun x _ y _ => forall₅_congr fun a b ha hb hab => ?_
  simp_rw [sub_le_iff_le_add, smul_eq_mul, aux_sub ha hb hab, mul_assoc, mul_left_comm]

Depends on / 依赖: and_congr_right, aux_sub, mul_assoc, mul_left_comm, simp_rw, smul_eq_mul, sub_le_iff_le_add
-/
lemma strongConvexOn_iff_convex :
    StrongConvexOn s m f ↔ ConvexOn Real s fun x => f x - m / (2 : Real) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ => forall₄_congr fun x _ y _ => forall₅_congr fun a b ha hb hab => ?_
  simp_rw [sub_le_iff_le_add, smul_eq_mul, aux_sub ha hb hab, mul_assoc, mul_left_comm]

/--
lemma `strongConcaveOn_iff_convex` / 引理 `strongConcaveOn_iff_convex`

English:
lemma strongConcaveOn_iff_convex
  proof: by
  refine and_congr_right fun _ => forall₄_congr fun x _ y _ => forall₅_congr fun a b ha hb hab => ?_
  simp_rw [← sub_le_iff_le_add, smul_eq_mul, aux_add ha hb hab, mul_assoc, mul_left_comm]

中文:
引理 strongConcaveOn_iff_convex
  证明: by
  refine and_congr_right fun _ => forall₄_congr fun x _ y _ => forall₅_congr fun a b ha hb hab => ?_
  simp_rw [← sub_le_iff_le_add, smul_eq_mul, aux_add ha hb hab, mul_assoc, mul_left_comm]

Depends on / 依赖: and_congr_right, aux_add, mul_assoc, mul_left_comm, simp_rw, smul_eq_mul, sub_le_iff_le_add
-/
lemma strongConcaveOn_iff_convex :
    StrongConcaveOn s m f ↔ ConcaveOn Real s fun x => f x + m / (2 : Real) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ => forall₄_congr fun x _ y _ => forall₅_congr fun a b ha hb hab => ?_
  simp_rw [← sub_le_iff_le_add, smul_eq_mul, aux_add ha hb hab, mul_assoc, mul_left_comm]

end InnerProductSpace
