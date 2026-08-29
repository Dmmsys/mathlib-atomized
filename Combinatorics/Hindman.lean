/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.Topology.Algebra.Semigroup
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Hindman's theorem on finite sums

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. There is also a stronger version, saying
that whenever a set of the form `FS(a₀, …)` is finitely colored, there exists a sequence
`b₀, b₁, b₂, …` such that `FS(b₀, …)` is monochromatic and contained in `FS(a₀, …)`. We prove both
these versions for a general semigroup `M` instead of `ℕ+` since it is no harder, although this
special case implies the general case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And with the help of a general topological argument one can show that any set
of the form `FS(a₀, …)` is `U`-large according to some idempotent ultrafilter `U` (see
`exists_idempotent_ultrafilter_le_FS`). This is enough to prove the theorem since in any finite
partition of a `U`-large set, one of the parts is `U`-large.

## Main results

- `FS_partition_regular`: the strong form of Hindman's theorem
- `exists_FS_of_finite_cover`: the weak form of Hindman's theorem

## Tags

Ramsey theory, ultrafilter

-/

@[expose] public section


open Filter

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[to_additive (attr := instance_reducible)
/-- Addition of ultrafilters given by `∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`. -/]
/--
Definition of `Ultrafilter.mul` / `Ultrafilter.mul` 的定义

English:
definition Ultrafilter.mul
  signature: {M} [Mul M]
  body: (· * ·) < > U <*> V

中文:
定义 Ultrafilter.mul
  签名: {M} [乘法 M]
  定义体: (· * ·) < > U <*> V
-/
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) < > U <*> V

attribute [local instance] Ultrafilter.mul Ultrafilter.add

/-- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive /-- We could have taken this as the definition of `U + V`, but then we would have to
prove that it defines an ultrafilter. -/]
/--
theorem `Ultrafilter.eventually_mul` / 定理 `Ultrafilter.eventually_mul`

English:
theorem Ultrafilter.eventually_mul
  given: {M} [Mul M] (U V : Ultrafilter M) (p : M -> Prop)
  proof: Iff.rfl

中文:
定理 Ultrafilter.eventually_mul
  条件: {M} [乘法 M] (U V : Ultrafilter M) (p : M -> 命题)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M -> Prop) :
    (forallᶠ m in ↑(U * V), p m) ↔ forallᶠ m in U, forallᶠ m' in V, p (m * m') :=
  Iff.rfl

/-- Semigroup structure on `Ultrafilter M` induced by a semigroup structure on `M`. -/
@[to_additive (attr := instance_reducible)
/-- Additive semigroup structure on `Ultrafilter M` induced by an additive semigroup
structure on `M`. -/]
/--
Definition of `Ultrafilter.semigroup` / `Ultrafilter.semigroup` 的定义

English:
definition Ultrafilter.semigroup
  signature: {M} [Semigroup M]
  body: { Ultrafilter.mul with
    mul_assoc := fun U V W =>
Ultrafilter.coe_inj.mp
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }

中文:
定义 Ultrafilter.semigroup
  签名: {M} [半群 M]
  定义体: { Ultrafilter.mul with
    mul_assoc := fun U V W =>
Ultrafilter.coe_inj.mp
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }

Depends on / 依赖: Filter, Filter.ext, Ultrafilter, Ultrafilter.coe_inj.mp, Ultrafilter.eventually_mul, Ultrafilter.mul, coe_inj, eventually_mul, mul_assoc
-/
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
Ultrafilter.coe_inj.mp
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

-- We don't prove `continuous_mul_right`, because in general it is false!
@[to_additive]
/--
theorem `Ultrafilter.continuous_mul_left` / 定理 `Ultrafilter.continuous_mul_left`

English:
theorem Ultrafilter.continuous_mul_left
  given: {M} [Mul M] (V : Ultrafilter M)
  proof: ultrafilterBasis_is_basis.continuous_iff.2 Set.forall_mem_range.mpr fun s =>
    ultrafilter_isOpen_basic { m : M | forallᶠ m' in V, m * m' in s }

中文:
定理 Ultrafilter.continuous_mul_left
  条件: {M} [乘法 M] (V : Ultrafilter M)
  证明: ultrafilterBasis_is_basis.continuous_iff.2 Set.forall_mem_range.mpr fun s =>
    ultrafilter_isOpen_basic { m : M | forallᶠ m' in V, m * m' in s }

Depends on / 依赖: Set.forall_mem_range.mpr, continuous_iff, forall_mem_range, ultrafilterBasis_is_basis, ultrafilterBasis_is_basis.continuous_iff, ultrafilter_isOpen_basic
-/
theorem Ultrafilter.continuous_mul_left {M} [Mul M] (V : Ultrafilter M) :
    Continuous (· * V) :=
ultrafilterBasis_is_basis.continuous_iff.2 Set.forall_mem_range.mpr fun s =>
    ultrafilter_isOpen_basic { m : M | forallᶠ m' in V, m * m' in s }

namespace Hindman

/--
Inductive type `FS` / 归纳类型 `FS`

English:
inductive FS
  parameters: {M} [AddSemigroup M]
  constructors (3):
    - head': (a : Stream' M) : FS a a.head
    - tail': (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
    - cons': (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)

中文:
归纳类型 FS
  参数: {M} [加法半群 M]
  构造子 (3 个):
    - head': (a : Stream' M) : FS a a.head
    - tail': (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
    - cons': (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)
-/
inductive FS {M} [AddSemigroup M] : Stream' M -> Set M
  | head' (a : Stream' M) : FS a a.head
  | tail' (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
  | cons' (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)

/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[to_additive FS]
/--
Inductive type `FP` / 归纳类型 `FP`

English:
inductive FP
  parameters: {M} [Semigroup M]
  constructors (3):
    - head': (a : Stream' M) : FP a a.head
    - tail': (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
    - cons': (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)

中文:
归纳类型 FP
  参数: {M} [半群 M]
  构造子 (3 个):
    - head': (a : Stream' M) : FP a a.head
    - tail': (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
    - cons': (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)
-/
inductive FP {M} [Semigroup M] : Stream' M -> Set M
  | head' (a : Stream' M) : FP a a.head
  | tail' (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
  | cons' (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)

section Aliases

/-! Since the constructors for `FS` and `FP` cheat using the `Set M = M → Prop` defeq,
we provide match patterns that preserve the defeq correctly in their type. -/

variable {M} [Semigroup M] (a : Stream' M) (m : M) (h : FP a.tail m)

set_option linter.defProp false in
/-- Constructor for `FP`. This is the preferred spelling over `FP.head'`. -/
@[to_additive (attr := match_pattern)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.head'`. -/]
/--
Definition of `FP.head` / `FP.head` 的定义

English:
abbreviation FP.head
  signature: : a.head in FP a
  body: FP.head' a

中文:
缩写 FP.head
  签名: : a.head in FP a
  定义体: FP.head' a

Depends on / 依赖: FP.head
-/
abbrev FP.head : a.head in FP a := FP.head' a
set_option linter.defProp false in
/-- Constructor for `FP`. This is the preferred spelling over `FP.tail'`. -/
@[to_additive (attr := match_pattern)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.tail'`. -/]
/--
Definition of `FP.tail` / `FP.tail` 的定义

English:
abbreviation FP.tail
  signature: : m in FP a
  body: FP.tail' a m h

中文:
缩写 FP.tail
  签名: : m in FP a
  定义体: FP.tail' a m h

Depends on / 依赖: FP.tail
-/
abbrev FP.tail : m in FP a := FP.tail' a m h
set_option linter.defProp false in
/-- Constructor for `FP`. This is the preferred spelling over `FP.cons'`. -/
@[to_additive (attr := match_pattern)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.cons'`. -/]
/--
Definition of `FP.cons` / `FP.cons` 的定义

English:
abbreviation FP.cons
  signature: : a.head * m in FP a
  body: FP.cons' a m h

中文:
缩写 FP.cons
  签名: : a.head * m in FP a
  定义体: FP.cons' a m h

Depends on / 依赖: FP.cons
-/
abbrev FP.cons : a.head * m in FP a := FP.cons' a m h

end Aliases

/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[to_additive /-- If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`
is obtained from a subsequence of `M` starting sufficiently late. -/]
/--
theorem `FP.mul` / 定理 `FP.mul`

English:
theorem FP.mul
  given: {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m in FP a)
  proof: by
  induction hm with
  | head' a => exact ⟨1, fun m hm => FP.cons a m hm⟩
  | tail' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    exact FP.tail _ _ (hn _ hm')
  | cons' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    rw [mul_assoc]
    exact FP.cons _ _ (hn _ hm')

@[to_additive exists_idempotent_ultrafilter_le_FS]

中文:
定理 FP.mul
  条件: {M} [半群 M] {a : Stream' M} {m : M} (hm : m in FP a)
  证明: by
  induction hm with
  | head' a => exact ⟨1, fun m hm => FP.cons a m hm⟩
  | tail' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    exact FP.tail _ _ (hn _ hm')
  | cons' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    rw [mul_assoc]
    exact FP.cons _ _ (hn _ hm')

@[to_additive exists_idempotent_ultrafilter_le_FS]

Depends on / 依赖: FP.cons, FP.tail, mul_assoc
-/
theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m in FP a) :
    exists n, forall m' in FP (a.drop n), m * m' in FP a := by
  induction hm with
  | head' a => exact ⟨1, fun m hm => FP.cons a m hm⟩
  | tail' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    exact FP.tail _ _ (hn _ hm')
  | cons' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    rw [mul_assoc]
    exact FP.cons _ _ (hn _ hm')

@[to_additive exists_idempotent_ultrafilter_le_FS]
/--
theorem `exists_idempotent_ultrafilter_le_FP` / 定理 `exists_idempotent_ultrafilter_le_FP`

English:
theorem exists_idempotent_ultrafilter_le_FP
  given: {M} [Semigroup M] (a : Stream' M)
  proof: by
  let S : Set (Ultrafilter M) := ⋂ n, { U | forallᶠ m in U, m in FP (a.drop n) }
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    refine ⟨U, U_idem, ?_⟩
    convert! Set.mem_iInter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n U hU
      filter_upwards [hU]
      rw [← Stream'.drop_drop]; rw [← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n
exact ⟨pure _, mem_pure.mpr FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).isCompact
    · intro n
      apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_ofPred_eq]; rw [Ultrafilter.eventually_mul]
    filter_upwards [hU n] with m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    filter_upwards [hV (n' + n)] with m' hm'
    apply hn
    simpa only [Stream'.drop_drop, add_comm] using hm'

@[to_additive exists_FS_of_large]

中文:
定理 存在_idempotent_ultrafilter_le_FP
  条件: {M} [半群 M] (a : Stream' M)
  证明: by
  let S : Set (Ultrafilter M) := ⋂ n, { U | forallᶠ m in U, m in FP (a.drop n) }
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    refine ⟨U, U_idem, ?_⟩
    convert! Set.mem_iInter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n U hU
      filter_upwards [hU]
      rw [← Stream'.drop_drop]; rw [← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n
exact ⟨pure _, mem_pure.mpr FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).isCompact
    · intro n
      apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_ofPred_eq]; rw [Ultrafilter.eventually_mul]
    filter_upwards [hU n] with m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    filter_upwards [hV (n' + n)] with m' hm'
    apply hn
    simpa only [Stream'.drop_drop, add_comm] using hm'

@[to_additive exists_FS_of_large]

Depends on / 依赖: FP.head, FP.tail, IsCompact, IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed, Set.mem_iInter.mp, Stream, U_idem, Ultrafilter, Ultrafilter.continuous_mul_left, a.drop, continuous_mul_left, convert, drop_drop, exists_idempotent_in_compact_subsemigroup, filter_upwards, mem_iInter, mem_pure, mem_pure.mpr, nonempty_iInter_of_sequence_nonempty_isCompact_isClosed, tail_eq_drop
-/
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) :
    exists U : Ultrafilter M, U * U = U ∧ forallᶠ m in U, m in FP a := by
  let S : Set (Ultrafilter M) := ⋂ n, { U | forallᶠ m in U, m in FP (a.drop n) }
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    refine ⟨U, U_idem, ?_⟩
    convert! Set.mem_iInter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n U hU
      filter_upwards [hU]
      rw [← Stream'.drop_drop]; rw [← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n
exact ⟨pure _, mem_pure.mpr FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).isCompact
    · intro n
      apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_ofPred_eq]; rw [Ultrafilter.eventually_mul]
    filter_upwards [hU n] with m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    filter_upwards [hV (n' + n)] with m' hm'
    apply hn
    simpa only [Stream'.drop_drop, add_comm] using hm'

@[to_additive exists_FS_of_large]
/--
theorem `exists_FP_of_large` / 定理 `exists_FP_of_large`

English:
theorem exists_FP_of_large
  statement: {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : Set M)
  proof: by
  /- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
  `U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
  let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again
  `U`-large, so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc.
  This gives the desired infinite sequence. -/
  have exists_elem : forall {s : Set M} (_hs : s in U), (s inter { m | forallᶠ m' in U, m * m' in s }).Nonempty :=
    fun {s} hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rwa [← U_idem] at hs)
  let elem : { s // s in U } -> M := fun p => (exists_elem p.property).some
  let succ : {s // s in U} -> {s // s in U} := fun (p : {s // s in U}) =>
        ⟨p.val inter {m : M | elem p * m in p.val},
         inter_mem p.property
           (show (exists_elem p.property).some in {m : M | forallᶠ (m' : M) in ↑U, m * m' in p.val} from
              p.val.inter_subset_right (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices forall (a : Stream' M), forall m in FP a, forall p, a = Stream'.corec elem succ p -> m in p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction h with
  | head' b =>
    rintro p rfl
    rw [Stream'.corec_eq]; rw [Stream'.head_cons]
    exact Set.inter_subset_left (Set.Nonempty.some_mem _)
  | tail' b n h ih =>
    rintro p rfl
    refine Set.inter_subset_left (ih (succ p) ?_)
    rw [Stream'.corec_eq]; rw [Stream'.tail_cons]
  | cons' b n h ih =>
    rintro p rfl
    have := Set.inter_subset_right (ih (succ p) ?_)
    · simpa only using! this
    rw [Stream'.corec_eq]; rw [Stream'.tail_cons]

中文:
定理 存在_FP_of_large
  结论: {M} [半群 M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : 集合 M)
  证明: by
  /- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
  `U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
  let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again
  `U`-large, so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc.
  This gives the desired infinite sequence. -/
  have exists_elem : forall {s : Set M} (_hs : s in U), (s inter { m | forallᶠ m' in U, m * m' in s }).Nonempty :=
    fun {s} hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rwa [← U_idem] at hs)
  let elem : { s // s in U } -> M := fun p => (exists_elem p.property).some
  let succ : {s // s in U} -> {s // s in U} := fun (p : {s // s in U}) =>
        ⟨p.val inter {m : M | elem p * m in p.val},
         inter_mem p.property
           (show (exists_elem p.property).some in {m : M | forallᶠ (m' : M) in ↑U, m * m' in p.val} from
              p.val.inter_subset_right (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices forall (a : Stream' M), forall m in FP a, forall p, a = Stream'.corec elem succ p -> m in p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction h with
  | head' b =>
    rintro p rfl
    rw [Stream'.corec_eq]; rw [Stream'.head_cons]
    exact Set.inter_subset_left (Set.Nonempty.some_mem _)
  | tail' b n h ih =>
    rintro p rfl
    refine Set.inter_subset_left (ih (succ p) ?_)
    rw [Stream'.corec_eq]; rw [Stream'.tail_cons]
  | cons' b n h ih =>
    rintro p rfl
    have := Set.inter_subset_right (ih (succ p) ?_)
    · simpa only using! this
    rw [Stream'.corec_eq]; rw [Stream'.tail_cons]
-/
theorem exists_FP_of_large {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : Set M)
    (sU : s₀ in U) : exists a, FP a subseteq s₀ := by
  /- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
  `U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
  let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again
  `U`-large, so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc.
  This gives the desired infinite sequence. -/
  have exists_elem : forall {s : Set M} (_hs : s in U), (s inter { m | forallᶠ m' in U, m * m' in s }).Nonempty :=
    fun {s} hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rwa [← U_idem] at hs)
  let elem : { s // s in U } -> M := fun p => (exists_elem p.property).some
  let succ : {s // s in U} -> {s // s in U} := fun (p : {s // s in U}) =>
        ⟨p.val inter {m : M | elem p * m in p.val},
         inter_mem p.property
           (show (exists_elem p.property).some in {m : M | forallᶠ (m' : M) in ↑U, m * m' in p.val} from
              p.val.inter_subset_right (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices forall (a : Stream' M), forall m in FP a, forall p, a = Stream'.corec elem succ p -> m in p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction h with
  | head' b =>
    rintro p rfl
    rw [Stream'.corec_eq]; rw [Stream'.head_cons]
    exact Set.inter_subset_left (Set.Nonempty.some_mem _)
  | tail' b n h ih =>
    rintro p rfl
    refine Set.inter_subset_left (ih (succ p) ?_)
    rw [Stream'.corec_eq]; rw [Stream'.tail_cons]
  | cons' b n h ih =>
    rintro p rfl
    have := Set.inter_subset_right (ih (succ p) ?_)
    · simpa only using! this
    rw [Stream'.corec_eq]; rw [Stream'.tail_cons]

/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[to_additive FS_partition_regular /-- The strong form of **Hindman's theorem**: in any finite
cover of an FS-set, one the parts contains an FS-set. -/]
/--
theorem `FP_partition_regular` / 定理 `FP_partition_regular`

English:
theorem FP_partition_regular
  statement: {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
  proof: let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩

中文:
定理 FP_partition_regular
  结论: {M} [半群 M] (a : Stream' M) (s : 集合 (集合 M)) (sfin : s.有限)
  证明: let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩

Depends on / 依赖: TotalSpace, TotalSpace.mk, Ultrafilter, Ultrafilter.finite_sUnion_mem_iff, exists_FP_of_large, exists_idempotent_ultrafilter_le_FP, finite_sUnion_mem_iff, mem_of_superset
-/
theorem FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
    (scov : FP a subseteq ⋃₀ s) : exists c in s, exists b : Stream' M, FP b subseteq c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[to_additive exists_FS_of_finite_cover /-- The weak form of **Hindman's theorem**: in any finite
cover of a nonempty additive semigroup, one of the parts contains an FS-set. -/]
/--
theorem `exists_FP_of_finite_cover` / 定理 `exists_FP_of_finite_cover`

English:
theorem exists_FP_of_finite_cover
  statement: {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
  proof: let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[to_additive FS_iter_tail_sub_FS]

中文:
定理 存在_FP_of_finite_cover
  结论: {M} [半群 M] [非空 M] (s : 集合 (集合 M)) (sfin : s.有限)
  证明: let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[to_additive FS_iter_tail_sub_FS]

Depends on / 依赖: Ultrafilter, Ultrafilter.continuous_mul_left, Ultrafilter.finite_sUnion_mem_iff, continuous_mul_left, exists_FP_of_large, exists_idempotent_of_compact_t2_of_continuous_mul_left, finite_sUnion_mem_iff, mem_of_superset, univ_mem
-/
theorem exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
    (scov : ⊤ subseteq ⋃₀ s) : exists c in s, exists a : Stream' M, FP a subseteq c :=
  let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[to_additive FS_iter_tail_sub_FS]
/--
theorem `FP_drop_subset_FP` / 定理 `FP_drop_subset_FP`

English:
theorem FP_drop_subset_FP
  given: {M} [Semigroup M] (a : Stream' M) (n : Nat)
  statement: FP (a.drop n) subseteq FP a
  proof: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Stream'.drop_drop]
    exact _root_.trans (FP.tail _) ih

@[to_additive]

中文:
定理 FP_drop_subset_FP
  条件: {M} [半群 M] (a : Stream' M) (n : 自然数)
  结论: FP (a.drop n) subseteq FP a
  证明: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Stream'.drop_drop]
    exact _root_.trans (FP.tail _) ih

@[to_additive]

Depends on / 依赖: FP.tail, Stream, _root_, _root_.trans, drop_drop
-/
theorem FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : Nat) : FP (a.drop n) subseteq FP a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Stream'.drop_drop]
    exact _root_.trans (FP.tail _) ih

@[to_additive]
/--
theorem `FP.singleton` / 定理 `FP.singleton`

English:
theorem FP.singleton
  given: {M} [Semigroup M] (a : Stream' M) (i : Nat)
  statement: a.get i in FP a
  proof: by
  induction i generalizing a with
  | zero => exact FP.head _
  | succ i ih => exact FP.tail _ _ (ih _)

@[to_additive]

中文:
定理 FP.singleton
  条件: {M} [半群 M] (a : Stream' M) (i : 自然数)
  结论: a.get i in FP a
  证明: by
  induction i generalizing a with
  | zero => exact FP.head _
  | succ i ih => exact FP.tail _ _ (ih _)

@[to_additive]

Depends on / 依赖: FP.head, FP.tail, generalizing
-/
theorem FP.singleton {M} [Semigroup M] (a : Stream' M) (i : Nat) : a.get i in FP a := by
  induction i generalizing a with
  | zero => exact FP.head _
  | succ i ih => exact FP.tail _ _ (ih _)

@[to_additive]
/--
theorem `FP.mul_two` / 定理 `FP.mul_two`

English:
theorem FP.mul_two
  given: {M} [Semigroup M] (a : Stream' M) (i j : Nat) (ij : i < j)
  proof: by
  refine FP_drop_subset_FP _ i ?_
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop]; rw [Stream'.get_drop]; rw [Stream'.get_drop] at this
  convert! this
  lia

@[to_additive]

中文:
定理 FP.mul_two
  条件: {M} [半群 M] (a : Stream' M) (i j : 自然数) (ij : i < j)
  证明: by
  refine FP_drop_subset_FP _ i ?_
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop]; rw [Stream'.get_drop]; rw [Stream'.get_drop] at this
  convert! this
  lia

@[to_additive]

Depends on / 依赖: FP.cons, FP.singleton, FP_drop_subset_FP, Nat.exists_eq_add_of_le, Nat.succ_le_of_lt, Stream, a.drop, convert, exists_eq_add_of_le, get_drop, head_drop, singleton, succ_le_of_lt, tail_eq_drop
-/
theorem FP.mul_two {M} [Semigroup M] (a : Stream' M) (i j : Nat) (ij : i < j) :
    a.get i * a.get j in FP a := by
  refine FP_drop_subset_FP _ i ?_
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop]; rw [Stream'.get_drop]; rw [Stream'.get_drop] at this
  convert! this
  lia

@[to_additive]
/--
theorem `FP.finsetProd` / 定理 `FP.finsetProd`

English:
theorem FP.finsetProd
  given: {M} [CommMonoid M] (a : Stream' M) (s : Finset Nat) (hs : s.Nonempty)
  proof: by
  refine FP_drop_subset_FP _ (s.min' hs) ?_
  induction s using Finset.eraseInduction with | H s ih => _
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs)]; rw [← Stream'.head_drop]
  rcases (s.erase (s.min' hs)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty, mul_one]
    exact FP.head _
  · apply FP.cons
    rw [Stream'.tail_eq_drop]; rw [Stream'.drop_drop]; rw [add_comm]
    refine Set.mem_of_subset_of_mem ?_ (ih _ (s.min'_mem hs) h)
    have : s.min' hs + 1 <= (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le this
    rw [hd]; rw [← Stream'.drop_drop]; rw [add_comm]
    apply FP_drop_subset_FP

@[deprecated (since := "2026-04-08")] alias FS.finset_sum := FS.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias FP.finset_prod := FP.finsetProd

中文:
定理 FP.finsetProd
  条件: {M} [交换幺半群 M] (a : Stream' M) (s : 有限集 自然数) (hs : s.非空)
  证明: by
  refine FP_drop_subset_FP _ (s.min' hs) ?_
  induction s using Finset.eraseInduction with | H s ih => _
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs)]; rw [← Stream'.head_drop]
  rcases (s.erase (s.min' hs)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty, mul_one]
    exact FP.head _
  · apply FP.cons
    rw [Stream'.tail_eq_drop]; rw [Stream'.drop_drop]; rw [add_comm]
    refine Set.mem_of_subset_of_mem ?_ (ih _ (s.min'_mem hs) h)
    have : s.min' hs + 1 <= (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le this
    rw [hd]; rw [← Stream'.drop_drop]; rw [add_comm]
    apply FP_drop_subset_FP

@[deprecated (since := "2026-04-08")] alias FS.finset_sum := FS.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias FP.finset_prod := FP.finsetProd

Depends on / 依赖: FP.cons, FP.head, FP_drop_subset_FP, Finset, Finset.eraseInduction, Finset.mul_prod_erase, Finset.prod_empty, Nat.succ_l, Set.mem_of_subset_of_mem, Stream, _mem, add_comm, drop_drop, eq_empty_or_nonempty, eraseInduction, head_drop, mem_of_subset_of_mem, mul_one, mul_prod_erase, prod_empty
-/
theorem FP.finsetProd {M} [CommMonoid M] (a : Stream' M) (s : Finset Nat) (hs : s.Nonempty) :
    (s.prod fun i => a.get i) in FP a := by
  refine FP_drop_subset_FP _ (s.min' hs) ?_
  induction s using Finset.eraseInduction with | H s ih => _
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs)]; rw [← Stream'.head_drop]
  rcases (s.erase (s.min' hs)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty, mul_one]
    exact FP.head _
  · apply FP.cons
    rw [Stream'.tail_eq_drop]; rw [Stream'.drop_drop]; rw [add_comm]
    refine Set.mem_of_subset_of_mem ?_ (ih _ (s.min'_mem hs) h)
    have : s.min' hs + 1 <= (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le this
    rw [hd]; rw [← Stream'.drop_drop]; rw [add_comm]
    apply FP_drop_subset_FP

@[deprecated (since := "2026-04-08")] alias FS.finset_sum := FS.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias FP.finset_prod := FP.finsetProd

end Hindman
