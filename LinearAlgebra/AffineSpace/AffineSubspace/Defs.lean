/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Defs

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

* `AffineSubspace k P` is the type of affine subspaces. Unlike affine spaces, affine subspaces are
  allowed to be empty, and lemmas that do not apply to empty affine subspaces have `Nonempty`
  hypotheses. There is a `CompleteLattice` structure on affine subspaces.
* `AffineSubspace.direction` gives the `Submodule` spanned by the pairwise differences of points
  in an `AffineSubspace`. There are various lemmas relating to the set of vectors in the
  `direction`, and relating the lattice structure on affine subspaces to that on their directions.
* `affineSpan` gives the affine subspace spanned by a set of points, with `vectorSpan` giving its
  direction. The `affineSpan` is defined in terms of `spanPoints`, which gives an explicit
  description of the points contained in the affine span; `spanPoints` itself should generally only
  be used when that description is required, with `affineSpan` being the main definition for other
  purposes. Two other descriptions of the affine span are proved equivalent: it is the `sInf` of
  affine subspaces containing the points, and (if `[Nontrivial k]`) it contains exactly those points
  that are affine combinations of points in the given set.

## Implementation notes

`outParam` is used in the definition of `AddTorsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by `P` or
`V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

@[expose] public section
noncomputable section

open Affine

open Set
open scoped Pointwise

section

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

/--
Definition of `vectorSpan` / `vectorSpan` 的定义

English:
definition vectorSpan
  signature: (s : Set P)
  body: Submodule.span k (s -ᵥ s)

中文:
定义 vectorSpan
  签名: (s : Set P)
  定义体: Submodule.span k (s -ᵥ s)

Depends on / 依赖: Submodule, Submodule.span
-/
def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

/--
theorem `vectorSpan_def` / 定理 `vectorSpan_def`

English:
theorem vectorSpan_def
  given: (s : Set P)
  statement: vectorSpan k s = Submodule.span k (s -ᵥ s)
  proof: rfl

中文:
定理 vectorSpan_def
  条件: (s : Set P)
  结论: vectorSpan k s = Submodule.span k (s -ᵥ s)
  证明: rfl
-/
theorem vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl

/--
theorem `vectorSpan_mono` / 定理 `vectorSpan_mono`

English:
theorem vectorSpan_mono
  given: {s₁ s₂ : Set P} (h : s₁ subseteq s₂)
  statement: vectorSpan k s₁ <= vectorSpan k s₂
  proof: Submodule.span_mono (vsub_self_mono h)

中文:
定理 vectorSpan_mono
  条件: {s₁ s₂ : Set P} (h : s₁ subseteq s₂)
  结论: vectorSpan k s₁ <= vectorSpan k s₂
  证明: Submodule.span_mono (vsub_self_mono h)

Depends on / 依赖: Submodule, Submodule.span_mono, span_mono, vsub_self_mono
-/
theorem vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : vectorSpan k s₁ <= vectorSpan k s₂ :=
  Submodule.span_mono (vsub_self_mono h)

variable (P) in
/-- The `vectorSpan` of the empty set is `⊥`. -/
@[simp]
/--
theorem `vectorSpan_empty` / 定理 `vectorSpan_empty`

English:
theorem vectorSpan_empty
  statement: vectorSpan k (∅ : Set P) = (⊥ : Submodule k V)
  proof: by
  rw [vectorSpan_def]; rw [vsub_empty]; rw [Submodule.span_empty]

中文:
定理 vectorSpan_empty
  结论: vectorSpan k (∅ : Set P) = (⊥ : Submodule k V)
  证明: by
  rw [vectorSpan_def]; rw [vsub_empty]; rw [Submodule.span_empty]

Depends on / 依赖: Submodule, Submodule.span_empty, span_empty, vectorSpan_def, vsub_empty
-/
theorem vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Submodule k V) := by
  rw [vectorSpan_def]; rw [vsub_empty]; rw [Submodule.span_empty]

/-- The `vectorSpan` of a single point is `⊥`. -/
@[simp]
/--
theorem `vectorSpan_singleton` / 定理 `vectorSpan_singleton`

English:
theorem vectorSpan_singleton
  given: (p : P)
  statement: vectorSpan k ({p} : Set P) = ⊥
  proof: by simp [vectorSpan_def]

中文:
定理 vectorSpan_singleton
  条件: (p : P)
  结论: vectorSpan k ({p} : Set P) = ⊥
  证明: by simp [vectorSpan_def]

Depends on / 依赖: vectorSpan_def
-/
theorem vectorSpan_singleton (p : P) : vectorSpan k ({p} : Set P) = ⊥ := by simp [vectorSpan_def]

/--
theorem `vsub_set_subset_vectorSpan` / 定理 `vsub_set_subset_vectorSpan`

English:
theorem vsub_set_subset_vectorSpan
  given: (s : Set P)
  statement: s -ᵥ s subseteq ↑(vectorSpan k s)
  proof: Submodule.subset_span

中文:
定理 vsub_set_subset_vectorSpan
  条件: (s : Set P)
  结论: s -ᵥ s subseteq ↑(vectorSpan k s)
  证明: Submodule.subset_span

Depends on / 依赖: Submodule, Submodule.subset_span, subset_span
-/
theorem vsub_set_subset_vectorSpan (s : Set P) : s -ᵥ s subseteq ↑(vectorSpan k s) :=
  Submodule.subset_span

/--
theorem `vsub_mem_vectorSpan` / 定理 `vsub_mem_vectorSpan`

English:
theorem vsub_mem_vectorSpan
  given: {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  proof: vsub_set_subset_vectorSpan k s (vsub_mem_vsub hp₁ hp₂)

中文:
定理 vsub_mem_vectorSpan
  条件: {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  证明: vsub_set_subset_vectorSpan k s (vsub_mem_vsub hp₁ hp₂)

Depends on / 依赖: vsub_mem_vsub, vsub_set_subset_vectorSpan
-/
theorem vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) :
    p₁ -ᵥ p₂ in vectorSpan k s :=
  vsub_set_subset_vectorSpan k s (vsub_mem_vsub hp₁ hp₂)

/--
lemma `vectorSpan_of_subsingleton` / 引理 `vectorSpan_of_subsingleton`

English:
lemma vectorSpan_of_subsingleton
  given: {s : Set P} (h : s.Subsingleton)
  statement: vectorSpan k s = ⊥
  proof: by
  rcases h.eq_empty_or_singleton with rfl | ⟨p, rfl⟩ <;> simp

@[simp]

中文:
引理 vectorSpan_of_subsingleton
  条件: {s : Set P} (h : s.Subsingleton)
  结论: vectorSpan k s = ⊥
  证明: by
  rcases h.eq_empty_or_singleton with rfl | ⟨p, rfl⟩ <;> simp

@[simp]

Depends on / 依赖: eq_empty_or_singleton, h.eq_empty_or_singleton
-/
lemma vectorSpan_of_subsingleton {s : Set P} (h : s.Subsingleton) : vectorSpan k s = ⊥ := by
  rcases h.eq_empty_or_singleton with rfl | ⟨p, rfl⟩ <;> simp

@[simp]
/--
lemma `vectorSpan_eq_bot_iff_subsingleton` / 引理 `vectorSpan_eq_bot_iff_subsingleton`

English:
lemma vectorSpan_eq_bot_iff_subsingleton
  given: {s : Set P}
  statement: vectorSpan k s = ⊥ ↔ s.Subsingleton
  proof: by
  refine ⟨fun h => ?_, vectorSpan_of_subsingleton _⟩
  by_contra hns
  rw [Set.not_subsingleton_iff] at hns
  obtain ⟨p, hp, q, hq, hpq⟩ := hns
  have hpq' := vsub_mem_vectorSpan k hp hq
  simp_all

中文:
引理 vectorSpan_eq_bot_iff_subsingleton
  条件: {s : Set P}
  结论: vectorSpan k s = ⊥ ↔ s.Subsingleton
  证明: by
  refine ⟨fun h => ?_, vectorSpan_of_subsingleton _⟩
  by_contra hns
  rw [Set.not_subsingleton_iff] at hns
  obtain ⟨p, hp, q, hq, hpq⟩ := hns
  have hpq' := vsub_mem_vectorSpan k hp hq
  simp_all

Depends on / 依赖: Set.not_subsingleton_iff, not_subsingleton_iff, vectorSpan_of_subsingleton, vsub_mem_vectorSpan
-/
lemma vectorSpan_eq_bot_iff_subsingleton {s : Set P} : vectorSpan k s = ⊥ ↔ s.Subsingleton := by
  refine ⟨fun h => ?_, vectorSpan_of_subsingleton _⟩
  by_contra hns
  rw [Set.not_subsingleton_iff] at hns
  obtain ⟨p, hp, q, hq, hpq⟩ := hns
  have hpq' := vsub_mem_vectorSpan k hp hq
  simp_all

/--
Definition of `spanPoints` / `spanPoints` 的定义

English:
definition spanPoints
  signature: (s : Set P)
  body: { p | exists p₁ in s, exists v in vectorSpan k s, p = v +ᵥ p₁ }

中文:
定义 spanPoints
  签名: (s : Set P)
  定义体: { p | exists p₁ in s, exists v in vectorSpan k s, p = v +ᵥ p₁ }

Depends on / 依赖: vectorSpan
-/
def spanPoints (s : Set P) : Set P :=
  { p | exists p₁ in s, exists v in vectorSpan k s, p = v +ᵥ p₁ }

/--
theorem `mem_spanPoints` / 定理 `mem_spanPoints`

English:
theorem mem_spanPoints
  given: (p : P) (s : Set P)
  statement: p in s -> p in spanPoints k s

中文:
定理 mem_spanPoints
  条件: (p : P) (s : Set P)
  结论: p in s -> p in spanPoints k s
-/
theorem mem_spanPoints (p : P) (s : Set P) : p in s -> p in spanPoints k s
  | hp => ⟨p, hp, 0, Submodule.zero_mem _, (zero_vadd V p).symm⟩

/--
theorem `subset_spanPoints` / 定理 `subset_spanPoints`

English:
theorem subset_spanPoints
  given: (s : Set P)
  statement: s subseteq spanPoints k s
  proof: fun p => mem_spanPoints k p s

中文:
定理 subset_spanPoints
  条件: (s : Set P)
  结论: s subseteq spanPoints k s
  证明: fun p => mem_spanPoints k p s

Depends on / 依赖: mem_spanPoints
-/
theorem subset_spanPoints (s : Set P) : s subseteq spanPoints k s := fun p => mem_spanPoints k p s

/-- The `spanPoints` of a set is nonempty if and only if that set is. -/
@[simp]
/--
theorem `spanPoints_nonempty` / 定理 `spanPoints_nonempty`

English:
theorem spanPoints_nonempty
  given: (s : Set P)
  statement: (spanPoints k s).Nonempty ↔ s.Nonempty
  proof: by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty]; rw [Set.not_nonempty_iff_eq_empty]
    intro h
    simp [h, spanPoints]
  · exact fun h => h.mono (subset_spanPoints _ _)

中文:
定理 spanPoints_nonempty
  条件: (s : Set P)
  结论: (spanPoints k s).Nonempty ↔ s.Nonempty
  证明: by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty]; rw [Set.not_nonempty_iff_eq_empty]
    intro h
    simp [h, spanPoints]
  · exact fun h => h.mono (subset_spanPoints _ _)

Depends on / 依赖: Set.not_nonempty_iff_eq_empty, contrapose, h.mono, not_nonempty_iff_eq_empty, spanPoints, subset_spanPoints
-/
theorem spanPoints_nonempty (s : Set P) : (spanPoints k s).Nonempty ↔ s.Nonempty := by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty]; rw [Set.not_nonempty_iff_eq_empty]
    intro h
    simp [h, spanPoints]
  · exact fun h => h.mono (subset_spanPoints _ _)

/--
theorem `vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan` / 定理 `vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan`

English:
theorem vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan
  statement: {s : Set P} {p : P} {v : V}
  proof: by
  rcases hp with ⟨p₂, ⟨hp₂, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₂p]; rw [vadd_vadd]
  exact ⟨p₂, hp₂, v + v₂, (vectorSpan k s).add_mem hv hv₂, rfl⟩

中文:
定理 vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan
  结论: {s : Set P} {p : P} {v : V}
  证明: by
  rcases hp with ⟨p₂, ⟨hp₂, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₂p]; rw [vadd_vadd]
  exact ⟨p₂, hp₂, v + v₂, (vectorSpan k s).add_mem hv hv₂, rfl⟩

Depends on / 依赖: add_mem, vadd_vadd, vectorSpan
-/
theorem vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p in spanPoints k s) (hv : v in vectorSpan k s) : v +ᵥ p in spanPoints k s := by
  rcases hp with ⟨p₂, ⟨hp₂, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₂p]; rw [vadd_vadd]
  exact ⟨p₂, hp₂, v + v₂, (vectorSpan k s).add_mem hv hv₂, rfl⟩

/--
theorem `vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints` / 定理 `vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints`

English:
theorem vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints
  statement: {s : Set P} {p₁ p₂ : P}
  proof: by
  rcases hp₁ with ⟨p₁a, ⟨hp₁a, ⟨v₁, ⟨hv₁, hv₁p⟩⟩⟩⟩
  rcases hp₂ with ⟨p₂a, ⟨hp₂a, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₁p]; rw [hv₂p]; rw [vsub_vadd_eq_vsub_sub (v₁ +ᵥ p₁a)]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [add_sub_assoc]
  have hv₁v₂ : v₁ - v₂ in vectorSpan k s := (vectorSpan k s).sub_mem hv₁ hv

中文:
定理 vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints
  结论: {s : Set P} {p₁ p₂ : P}
  证明: by
  rcases hp₁ with ⟨p₁a, ⟨hp₁a, ⟨v₁, ⟨hv₁, hv₁p⟩⟩⟩⟩
  rcases hp₂ with ⟨p₂a, ⟨hp₂a, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₁p]; rw [hv₂p]; rw [vsub_vadd_eq_vsub_sub (v₁ +ᵥ p₁a)]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [add_sub_assoc]
  have hv₁v₂ : v₁ - v₂ in vectorSpan k s := (vectorSpan k s).sub_mem hv₁ hv

Depends on / 依赖: add_comm, add_mem, add_sub_assoc, sub_mem, vadd_vsub_assoc, vectorSpan, vsub_mem_vectorSpan, vsub_vadd_eq_vsub_sub
-/
theorem vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ in spanPoints k s) (hp₂ : p₂ in spanPoints k s) : p₁ -ᵥ p₂ in vectorSpan k s := by
  rcases hp₁ with ⟨p₁a, ⟨hp₁a, ⟨v₁, ⟨hv₁, hv₁p⟩⟩⟩⟩
  rcases hp₂ with ⟨p₂a, ⟨hp₂a, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₁p]; rw [hv₂p]; rw [vsub_vadd_eq_vsub_sub (v₁ +ᵥ p₁a)]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [add_sub_assoc]
  have hv₁v₂ : v₁ - v₂ in vectorSpan k s := (vectorSpan k s).sub_mem hv₁ hv₂
  refine (vectorSpan k s).add_mem ?_ hv₁v₂
  exact vsub_mem_vectorSpan k hp₁a hp₂a

end

/--
Definition of `AffineSubspace` / `AffineSubspace` 的定义

English:
structure AffineSubspace
  parameters: (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V]
  axioms and operations (2):
    - carrier : Set P
    - smul_vsub_vadd_mem'((c : k) {p₁ p₂ p₃ : P}) : p₁ in carrier -> p₂ in carrier -> p₃ in carrier -> c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ in carrier

中文:
结构 AffineSubspace
  参数: (k : 类型) {V : 类型} (P : 类型) [Ring k] [AddCommGroup V]
  公理与运算 (2 个):
    - carrier : Set P
    - smul_vsub_vadd_mem'((c : k) {p₁ p₂ p₃ : P}) : p₁ in carrier -> p₂ in carrier -> p₃ in carrier -> c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ in carrier
-/
structure AffineSubspace (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V]
  [Module k V] [AffineSpace V P] where
  /-- The affine subspace seen as a subset. -/
  carrier : Set P
  protected smul_vsub_vadd_mem' (c : k) {p₁ p₂ p₃ : P} :
    p₁ in carrier -> p₂ in carrier -> p₃ in carrier -> c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ in carrier

namespace AffineSubspace

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (AffineSubspace k P) P
  body: carrier
  coe_injective p q _ := by cases p; cases q; congr

中文:
实例 :
  签名: SetLike (AffineSubspace k P) P
  定义体: carrier
  coe_injective p q _ := by cases p; cases q; congr

Depends on / 依赖: carrier
-/
instance : SetLike (AffineSubspace k P) P where
  coe := carrier
  coe_injective p q _ := by cases p; cases q; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (AffineSubspace k P)
  body: .ofSetLike (AffineSubspace k P) P

中文:
实例 :
  签名: PartialOrder (AffineSubspace k P)
  定义体: .ofSetLike (AffineSubspace k P) P

Depends on / 依赖: AffineSubspace, ofSetLike
-/
instance : PartialOrder (AffineSubspace k P) := .ofSetLike (AffineSubspace k P) P

/--
lemma `carrier_eq_coe` / 引理 `carrier_eq_coe`

English:
lemma carrier_eq_coe
  given: (s : AffineSubspace k P)
  statement: s.carrier = s
  proof: rfl

中文:
引理 carrier_eq_coe
  条件: (s : AffineSubspace k P)
  结论: s.carrier = s
  证明: rfl
-/
@[simp] lemma carrier_eq_coe (s : AffineSubspace k P) : s.carrier = s := rfl

/--
lemma `smul_vsub_vadd_mem` / 引理 `smul_vsub_vadd_mem`

English:
lemma smul_vsub_vadd_mem
  given: (s : AffineSubspace k P) (c : k) {p₁ p₂ p₃ : P}
  proof: s.smul_vsub_vadd_mem' c

中文:
引理 smul_vsub_vadd_mem
  条件: (s : AffineSubspace k P) (c : k) {p₁ p₂ p₃ : P}
  证明: s.smul_vsub_vadd_mem' c

Depends on / 依赖: s.smul_vsub_vadd_mem, smul_vsub_vadd_mem
-/
lemma smul_vsub_vadd_mem (s : AffineSubspace k P) (c : k) {p₁ p₂ p₃ : P} :
    p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ in s :=
  s.smul_vsub_vadd_mem' c

/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: (p : P) (s : AffineSubspace k P)
  statement: p in (s : Set P) ↔ p in s
  proof: by simp

中文:
定理 mem_coe
  条件: (p : P) (s : AffineSubspace k P)
  结论: p in (s : Set P) ↔ p in s
  证明: by simp
-/
theorem mem_coe (p : P) (s : AffineSubspace k P) : p in (s : Set P) ↔ p in s := by simp

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : AffineSubspace k P -> Set P)
  proof: SetLike.coe_injective

@[ext (iff := false)]

中文:
定理 coe_injective
  结论: Function.Injective ((↑) : AffineSubspace k P -> Set P)
  证明: SetLike.coe_injective

@[ext (iff := false)]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective ((↑) : AffineSubspace k P -> Set P) :=
  SetLike.coe_injective

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : AffineSubspace k P} (h : forall x, x in p ↔ x in q)
  statement: p = q
  proof: SetLike.ext h

中文:
定理 ext
  条件: {p q : AffineSubspace k P} (h : 对任意 x, x in p ↔ x in q)
  结论: p = q
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {p q : AffineSubspace k P} (h : forall x, x in p ↔ x in q) : p = q :=
  SetLike.ext h

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (s₁ s₂ : AffineSubspace k P)
  statement: s₁ = s₂ ↔ (s₁ : Set P) = s₂
  proof: SetLike.ext'_iff

中文:
定理 ext_iff
  条件: (s₁ s₂ : AffineSubspace k P)
  结论: s₁ = s₂ ↔ (s₁ : Set P) = s₂
  证明: SetLike.ext'_iff
-/
protected theorem ext_iff (s₁ s₂ : AffineSubspace k P) : s₁ = s₂ ↔ (s₁ : Set P) = s₂ :=
  SetLike.ext'_iff

end AffineSubspace

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

/--
Definition of `toAffineSubspace` / `toAffineSubspace` 的定义

English:
definition toAffineSubspace
  signature: (p : Submodule k V)
  body: p
  smul_vsub_vadd_mem' _ _ _ _ h₁ h₂ h₃ := p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃

中文:
定义 toAffineSubspace
  签名: (p : Submodule k V)
  定义体: p
  smul_vsub_vadd_mem' _ _ _ _ h₁ h₂ h₃ := p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃
-/
@[coe] def toAffineSubspace (p : Submodule k V) : AffineSubspace k V where
  carrier := p
  smul_vsub_vadd_mem' _ _ _ _ h₁ h₂ h₃ := p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Submodule k V) (AffineSubspace k V)
  body: ⟨toAffineSubspace⟩

@[simp]

中文:
实例 :
  签名: Coe (Submodule k V) (AffineSubspace k V)
  定义体: ⟨toAffineSubspace⟩

@[simp]

Depends on / 依赖: toAffineSubspace
-/
instance : Coe (Submodule k V) (AffineSubspace k V) := ⟨toAffineSubspace⟩

@[simp]
/--
theorem `mem_toAffineSubspace` / 定理 `mem_toAffineSubspace`

English:
theorem mem_toAffineSubspace
  given: {p : Submodule k V} {x : V}
  proof: Iff.rfl

中文:
定理 mem_toAffineSubspace
  条件: {p : Submodule k V} {x : V}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAffineSubspace {p : Submodule k V} {x : V} :
    x in (p : AffineSubspace k V) ↔ x in p := Iff.rfl

end Submodule

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/--
lemma `vsub_self_of_zero_mem` / 引理 `vsub_self_of_zero_mem`

English:
lemma vsub_self_of_zero_mem
  given: {s : AffineSubspace k V} (hs : 0 in s)
  proof: by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using s.smul_vsub_vadd_mem 1 ha hb hs
  · exact fun h => ⟨x, h, 0, hs, by simp⟩

中文:
引理 vsub_self_of_zero_mem
  条件: {s : AffineSubspace k V} (hs : 0 in s)
  证明: by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using s.smul_vsub_vadd_mem 1 ha hb hs
  · exact fun h => ⟨x, h, 0, hs, by simp⟩

Depends on / 依赖: s.smul_vsub_vadd_mem, smul_vsub_vadd_mem
-/
lemma vsub_self_of_zero_mem {s : AffineSubspace k V} (hs : 0 in s) :
    (s : Set V) -ᵥ s = s := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using s.smul_vsub_vadd_mem 1 ha hb hs
  · exact fun h => ⟨x, h, 0, hs, by simp⟩

/--
lemma `vsub_self_eq_iff_zero_mem` / 引理 `vsub_self_eq_iff_zero_mem`

English:
lemma vsub_self_eq_iff_zero_mem
  given: {s : AffineSubspace k V} [Nonempty s]
  proof: by
  refine ⟨fun h => ?_, vsub_self_of_zero_mem⟩
  obtain x : s := Classical.choice inferInstance
  suffices (x : V) - x in (s : Set _) by aesop
  rw [← h]; rw [mem_vsub]
  aesop

中文:
引理 vsub_self_eq_iff_zero_mem
  条件: {s : AffineSubspace k V} [Nonempty s]
  证明: by
  refine ⟨fun h => ?_, vsub_self_of_zero_mem⟩
  obtain x : s := Classical.choice inferInstance
  suffices (x : V) - x in (s : Set _) by aesop
  rw [← h]; rw [mem_vsub]
  aesop
-/
@[simp] lemma vsub_self_eq_iff_zero_mem {s : AffineSubspace k V} [Nonempty s] :
    (s : Set V) -ᵥ s = s ↔ 0 in s := by
  refine ⟨fun h => ?_, vsub_self_of_zero_mem⟩
  obtain x : s := Classical.choice inferInstance
  suffices (x : V) - x in (s : Set _) by aesop
  rw [← h]; rw [mem_vsub]
  aesop

/--
Definition of `direction` / `direction` 的定义

English:
definition direction
  signature: (s : AffineSubspace k P)
  body: vectorSpan k (s : Set P)

中文:
定义 direction
  签名: (s : AffineSubspace k P)
  定义体: vectorSpan k (s : Set P)

Depends on / 依赖: vectorSpan
-/
def direction (s : AffineSubspace k P) : Submodule k V :=
  vectorSpan k (s : Set P)

/--
theorem `direction_eq_vectorSpan` / 定理 `direction_eq_vectorSpan`

English:
theorem direction_eq_vectorSpan
  given: (s : AffineSubspace k P)
  statement: s.direction = vectorSpan k (s : Set P)
  proof: rfl

中文:
定理 direction_eq_vectorSpan
  条件: (s : AffineSubspace k P)
  结论: s.direction = vectorSpan k (s : Set P)
  证明: rfl
-/
theorem direction_eq_vectorSpan (s : AffineSubspace k P) : s.direction = vectorSpan k (s : Set P) :=
  rfl

/--
Definition of `directionOfNonempty` / `directionOfNonempty` 的定义

English:
definition directionOfNonempty
  signature: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  body: (s : Set P) -ᵥ s
  zero_mem' := by
    obtain ⟨p, hp⟩ := h
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    rintro _ _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩ ⟨p₃, hp₃, p₄, hp₄, rfl⟩
    rw [← vadd_vsub_assoc]
    refine vsub_mem_vsub ?_ hp₄
    rw [mem_coe]
    convert s.smul_vsub_vadd_mem 1 hp₁ hp

中文:
定义 directionOfNonempty
  签名: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  定义体: (s : Set P) -ᵥ s
  zero_mem' := by
    obtain ⟨p, hp⟩ := h
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    rintro _ _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩ ⟨p₃, hp₃, p₄, hp₄, rfl⟩
    rw [← vadd_vsub_assoc]
    refine vsub_mem_vsub ?_ hp₄
    rw [mem_coe]
    convert s.smul_vsub_vadd_mem 1 hp₁ hp
-/
def directionOfNonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : Submodule k V where
  carrier := (s : Set P) -ᵥ s
  zero_mem' := by
    obtain ⟨p, hp⟩ := h
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    rintro _ _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩ ⟨p₃, hp₃, p₄, hp₄, rfl⟩
    rw [← vadd_vsub_assoc]
    refine vsub_mem_vsub ?_ hp₄
    rw [mem_coe]
    convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp₃
    rw [one_smul]
  smul_mem' := by
    rintro c _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    rw [← vadd_vsub (c • (p₁ -ᵥ p₂)) p₂]
    refine vsub_mem_vsub ?_ hp₂
    exact s.smul_vsub_vadd_mem c hp₁ hp₂ hp₂

/--
theorem `directionOfNonempty_eq_direction` / 定理 `directionOfNonempty_eq_direction`

English:
theorem directionOfNonempty_eq_direction
  given: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  proof: by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe]; rw [directionOfNonempty]; rw [direction]; rw [Submodule.coe_set_mk]; rw [AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

中文:
定理 directionOfNonempty_eq_direction
  条件: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  证明: by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe]; rw [directionOfNonempty]; rw [direction]; rw [Submodule.coe_set_mk]; rw [AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

Depends on / 依赖: AddSubmonoid, AddSubmonoid.coe_set_mk, Set.Subset.rfl, SetLike, SetLike.coe_subset_coe, Submodule, Submodule.coe_set_mk, Submodule.span_le, Subset, coe_set_mk, coe_subset_coe, direction, directionOfNonempty, le_antisymm, span_le, vsub_set_subset_vectorSpan
-/
theorem directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    directionOfNonempty h = s.direction := by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe]; rw [directionOfNonempty]; rw [direction]; rw [Submodule.coe_set_mk]; rw [AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

/--
theorem `coe_direction_eq_vsub_set` / 定理 `coe_direction_eq_vsub_set`

English:
theorem coe_direction_eq_vsub_set
  given: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  proof: directionOfNonempty_eq_direction h ▸ rfl

中文:
定理 coe_direction_eq_vsub_set
  条件: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  证明: directionOfNonempty_eq_direction h ▸ rfl

Depends on / 依赖: directionOfNonempty_eq_direction
-/
theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s :=
  directionOfNonempty_eq_direction h ▸ rfl

/--
theorem `mem_direction_iff_eq_vsub` / 定理 `mem_direction_iff_eq_vsub`

English:
theorem mem_direction_iff_eq_vsub
  given: {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V)
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set h]; rw [Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

中文:
定理 mem_direction_iff_eq_vsub
  条件: {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V)
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set h]; rw [Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

Depends on / 依赖: Set.mem_vsub, SetLike, SetLike.mem_coe, coe_direction_eq_vsub_set, eq_comm, mem_coe, mem_vsub
-/
theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v in s.direction ↔ exists p₁ in s, exists p₂ in s, v = p₁ -ᵥ p₂ := by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set h]; rw [Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

/--
theorem `vadd_mem_of_mem_direction` / 定理 `vadd_mem_of_mem_direction`

English:
theorem vadd_mem_of_mem_direction
  statement: {s : AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P}
  proof: by
  rw [mem_direction_iff_eq_vsub ⟨p]; rw [hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

中文:
定理 vadd_mem_of_mem_direction
  结论: {s : AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P}
  证明: by
  rw [mem_direction_iff_eq_vsub ⟨p]; rw [hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

Depends on / 依赖: convert, mem_direction_iff_eq_vsub, one_smul, s.smul_vsub_vadd_mem, smul_vsub_vadd_mem
-/
theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P}
    (hp : p in s) : v +ᵥ p in s := by
  rw [mem_direction_iff_eq_vsub ⟨p]; rw [hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

/--
theorem `vsub_mem_direction` / 定理 `vsub_mem_direction`

English:
theorem vsub_mem_direction
  given: {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  proof: vsub_mem_vectorSpan k hp₁ hp₂

中文:
定理 vsub_mem_direction
  条件: {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  证明: vsub_mem_vectorSpan k hp₁ hp₂

Depends on / 依赖: vsub_mem_vectorSpan
-/
theorem vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) :
    p₁ -ᵥ p₂ in s.direction :=
  vsub_mem_vectorSpan k hp₁ hp₂

/--
theorem `vadd_mem_iff_mem_direction` / 定理 `vadd_mem_iff_mem_direction`

English:
theorem vadd_mem_iff_mem_direction
  given: {s : AffineSubspace k P} (v : V) {p : P} (hp : p in s)
  proof: ⟨fun h => by simpa using vsub_mem_direction h hp, fun h => vadd_mem_of_mem_direction h hp⟩

中文:
定理 vadd_mem_iff_mem_direction
  条件: {s : AffineSubspace k P} (v : V) {p : P} (hp : p in s)
  证明: ⟨fun h => by simpa using vsub_mem_direction h hp, fun h => vadd_mem_of_mem_direction h hp⟩

Depends on / 依赖: vadd_mem_of_mem_direction, vsub_mem_direction
-/
theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p in s) :
    v +ᵥ p in s ↔ v in s.direction :=
  ⟨fun h => by simpa using vsub_mem_direction h hp, fun h => vadd_mem_of_mem_direction h hp⟩

/--
theorem `vadd_mem_iff_mem_of_mem_direction` / 定理 `vadd_mem_iff_mem_of_mem_direction`

English:
theorem vadd_mem_iff_mem_of_mem_direction
  statement: {s : AffineSubspace k P} {v : V} (hv : v in s.direction)
  proof: by
  refine ⟨fun h => ?_, fun h => vadd_mem_of_mem_direction hv h⟩
  convert! vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

中文:
定理 vadd_mem_iff_mem_of_mem_direction
  结论: {s : AffineSubspace k P} {v : V} (hv : v in s.direction)
  证明: by
  refine ⟨fun h => ?_, fun h => vadd_mem_of_mem_direction hv h⟩
  convert! vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

Depends on / 依赖: Submodule, Submodule.neg_mem, convert, neg_mem, vadd_mem_of_mem_direction
-/
theorem vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v in s.direction)
    {p : P} : v +ᵥ p in s ↔ p in s := by
  refine ⟨fun h => ?_, fun h => vadd_mem_of_mem_direction hv h⟩
  convert! vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

/--
theorem `coe_direction_eq_vsub_set_right` / 定理 `coe_direction_eq_vsub_set_right`

English:
theorem coe_direction_eq_vsub_set_right
  given: {s : AffineSubspace k P} {p : P} (hp : p in s)
  proof: by
  rw [coe_direction_eq_vsub_set ⟨p]; rw [hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      vadd_mem_of_mem_direction (vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

中文:
定理 coe_direction_eq_vsub_set_right
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s)
  证明: by
  rw [coe_direction_eq_vsub_set ⟨p]; rw [hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      vadd_mem_of_mem_direction (vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

Depends on / 依赖: coe_direction_eq_vsub_set, le_antisymm, vadd_mem_of_mem_direction, vadd_vsub, vsub_mem_direction
-/
theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p in s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  rw [coe_direction_eq_vsub_set ⟨p]; rw [hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      vadd_mem_of_mem_direction (vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

/--
theorem `coe_direction_eq_vsub_set_left` / 定理 `coe_direction_eq_vsub_set_left`

English:
theorem coe_direction_eq_vsub_set_left
  given: {s : AffineSubspace k P} {p : P} (hp : p in s)
  proof: by
  ext v
  rw [SetLike.mem_coe]; rw [← Submodule.neg_mem_iff]; rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_right hp]; rw [Set.mem_image]; rw [Set.mem_image]
  conv_lhs =>
    congr
    ext
    rw [← neg_vsub_eq_vsub_rev]; rw [neg_inj]

中文:
定理 coe_direction_eq_vsub_set_left
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s)
  证明: by
  ext v
  rw [SetLike.mem_coe]; rw [← Submodule.neg_mem_iff]; rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_right hp]; rw [Set.mem_image]; rw [Set.mem_image]
  conv_lhs =>
    congr
    ext
    rw [← neg_vsub_eq_vsub_rev]; rw [neg_inj]

Depends on / 依赖: Set.mem_image, SetLike, SetLike.mem_coe, Submodule, Submodule.neg_mem_iff, coe_direction_eq_vsub_set_right, conv_lhs, mem_coe, mem_image, neg_inj, neg_mem_iff, neg_vsub_eq_vsub_rev
-/
theorem coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p in s) :
    (s.direction : Set V) = (p -ᵥ ·) '' s := by
  ext v
  rw [SetLike.mem_coe]; rw [← Submodule.neg_mem_iff]; rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_right hp]; rw [Set.mem_image]; rw [Set.mem_image]
  conv_lhs =>
    congr
    ext
    rw [← neg_vsub_eq_vsub_rev]; rw [neg_inj]

/--
theorem `mem_direction_iff_eq_vsub_right` / 定理 `mem_direction_iff_eq_vsub_right`

English:
theorem mem_direction_iff_eq_vsub_right
  given: {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V)
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

中文:
定理 mem_direction_iff_eq_vsub_right
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V)
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_direction_eq_vsub_set_right, hv.symm, mem_coe
-/
theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V) :
    v in s.direction ↔ exists p₂ in s, v = p₂ -ᵥ p := by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

/--
theorem `mem_direction_iff_eq_vsub_left` / 定理 `mem_direction_iff_eq_vsub_left`

English:
theorem mem_direction_iff_eq_vsub_left
  given: {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V)
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

中文:
定理 mem_direction_iff_eq_vsub_left
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V)
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_direction_eq_vsub_set_left, hv.symm, mem_coe
-/
theorem mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V) :
    v in s.direction ↔ exists p₂ in s, v = p -ᵥ p₂ := by
  rw [← SetLike.mem_coe]; rw [coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

/--
lemma `direction_eq_self_iff_zero_mem` / 引理 `direction_eq_self_iff_zero_mem`

English:
lemma direction_eq_self_iff_zero_mem
  given: {s : AffineSubspace k V}
  proof: by rw [← h]; simp
  mpr h := by
    ext x
    rw [Submodule.mem_toAffineSubspace]; rw [← SetLike.mem_coe]
    simp [s.coe_direction_eq_vsub_set ⟨0, h⟩, vsub_self_of_zero_mem h]

中文:
引理 direction_eq_self_iff_zero_mem
  条件: {s : AffineSubspace k V}
  证明: by rw [← h]; simp
  mpr h := by
    ext x
    rw [Submodule.mem_toAffineSubspace]; rw [← SetLike.mem_coe]
    simp [s.coe_direction_eq_vsub_set ⟨0, h⟩, vsub_self_of_zero_mem h]
-/
@[simp] lemma direction_eq_self_iff_zero_mem {s : AffineSubspace k V} :
    s.direction = s ↔ 0 in s where
  mp h := by rw [← h]; simp
  mpr h := by
    ext x
    rw [Submodule.mem_toAffineSubspace]; rw [← SetLike.mem_coe]
    simp [s.coe_direction_eq_vsub_set ⟨0, h⟩, vsub_self_of_zero_mem h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (AffineSubspace k V) (Submodule k V) (·) (0 in ·)
  body: ⟨fun _ hs => ⟨_, direction_eq_self_iff_zero_mem.mpr hs⟩⟩

中文:
实例 :
  签名: CanLift (AffineSubspace k V) (Submodule k V) (·) (0 in ·)
  定义体: ⟨fun _ hs => ⟨_, direction_eq_self_iff_zero_mem.mpr hs⟩⟩

Depends on / 依赖: direction_eq_self_iff_zero_mem, direction_eq_self_iff_zero_mem.mpr
-/
instance : CanLift (AffineSubspace k V) (Submodule k V) (·) (0 in ·) :=
  ⟨fun _ hs => ⟨_, direction_eq_self_iff_zero_mem.mpr hs⟩⟩

/--
theorem `ext_of_direction_eq` / 定理 `ext_of_direction_eq`

English:
theorem ext_of_direction_eq
  statement: {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
  proof: by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd

中文:
定理 ext_of_direction_eq
  结论: {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
  证明: by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd

Depends on / 依赖: Set.mem_of_mem_inter_left, Set.mem_of_mem_inter_right, hn.some, hn.some_mem, mem_of_mem_inter_left, mem_of_mem_inter_right, some_mem, vadd_mem_of_mem_direction, vsub_mem_direction, vsub_vadd
-/
theorem ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : ((s₁ : Set P) inter s₂).Nonempty) : s₁ = s₂ := by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq1
    rw [hd]
    exact vsub_mem_direction hp hq2

/--
theorem `eq_iff_direction_eq_of_mem` / 定理 `eq_iff_direction_eq_of_mem`

English:
theorem eq_iff_direction_eq_of_mem
  statement: {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁)
  proof: ⟨fun h => h ▸ rfl, fun h => ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

中文:
定理 eq_iff_direction_eq_of_mem
  结论: {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁)
  证明: ⟨fun h => h ▸ rfl, fun h => ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

Depends on / 依赖: ext_of_direction_eq
-/
theorem eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁)
    (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction :=
  ⟨fun h => h ▸ rfl, fun h => ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (p : P) (direction : Submodule k V)
  body: { q | q -ᵥ p in direction }
  smul_vsub_vadd_mem' c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simpa [vadd_vsub_assoc] using
      direction.add_mem (direction.smul_mem c (direction.sub_mem hp₁ hp₂)) hp₃

中文:
定义 mk'
  签名: (p : P) (direction : Submodule k V)
  定义体: { q | q -ᵥ p in direction }
  smul_vsub_vadd_mem' c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simpa [vadd_vsub_assoc] using
      direction.add_mem (direction.smul_mem c (direction.sub_mem hp₁ hp₂)) hp₃

Depends on / 依赖: direction
-/
def mk' (p : P) (direction : Submodule k V) : AffineSubspace k P where
  carrier := { q | q -ᵥ p in direction }
  smul_vsub_vadd_mem' c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simpa [vadd_vsub_assoc] using
      direction.add_mem (direction.smul_mem c (direction.sub_mem hp₁ hp₂)) hp₃

/-- A point lies in an affine subspace constructed from another point and a direction if and only
if their difference is in that direction. -/
@[simp]
/--
theorem `mem_mk'` / 定理 `mem_mk'`

English:
theorem mem_mk'
  given: {p q : P} {direction : Submodule k V}
  statement: q in mk' p direction ↔ q -ᵥ p in direction
  proof: Iff.rfl

中文:
定理 mem_mk'
  条件: {p q : P} {direction : Submodule k V}
  结论: q in mk' p direction ↔ q -ᵥ p in direction
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk' {p q : P} {direction : Submodule k V} : q in mk' p direction ↔ q -ᵥ p in direction :=
  Iff.rfl

/--
theorem `self_mem_mk'` / 定理 `self_mem_mk'`

English:
theorem self_mem_mk'
  given: (p : P) (direction : Submodule k V)
  statement: p in mk' p direction
  proof: by
  simp

中文:
定理 self_mem_mk'
  条件: (p : P) (direction : Submodule k V)
  结论: p in mk' p direction
  证明: by
  simp
-/
theorem self_mem_mk' (p : P) (direction : Submodule k V) : p in mk' p direction := by
  simp

/--
theorem `vadd_mem_mk'` / 定理 `vadd_mem_mk'`

English:
theorem vadd_mem_mk'
  given: {v : V} (p : P) {direction : Submodule k V} (hv : v in direction)
  proof: by
  simpa

中文:
定理 vadd_mem_mk'
  条件: {v : V} (p : P) {direction : Submodule k V} (hv : v in direction)
  证明: by
  simpa
-/
theorem vadd_mem_mk' {v : V} (p : P) {direction : Submodule k V} (hv : v in direction) :
    v +ᵥ p in mk' p direction := by
  simpa

/--
theorem `mk'_nonempty` / 定理 `mk'_nonempty`

English:
theorem mk'_nonempty
  given: (p : P) (direction : Submodule k V)
  statement: (mk' p direction : Set P).Nonempty
  proof: ⟨p, self_mem_mk' p direction⟩

中文:
定理 mk'_nonempty
  条件: (p : P) (direction : Submodule k V)
  结论: (mk' p direction : Set P).Nonempty
  证明: ⟨p, self_mem_mk' p direction⟩
-/
theorem mk'_nonempty (p : P) (direction : Submodule k V) : (mk' p direction : Set P).Nonempty :=
  ⟨p, self_mem_mk' p direction⟩

instance (p : P) (direction : Submodule k V) : Nonempty (mk' p direction) :=
  ⟨⟨p, self_mem_mk' p direction⟩⟩

/-- The direction of an affine subspace constructed from a point and a direction. -/
@[simp]
/--
theorem `direction_mk'` / 定理 `direction_mk'`

English:
theorem direction_mk'
  given: (p : P) (direction : Submodule k V)
  proof: by
  ext v
  rw [mem_direction_iff_eq_vsub (mk'_nonempty _ _)]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    simpa using direction.sub_mem hp₁ hp₂
  · exact fun hv => ⟨v +ᵥ p, vadd_mem_mk' _ hv, p, self_mem_mk' _ _, (vadd_vsub _ _).symm⟩

中文:
定理 direction_mk'
  条件: (p : P) (direction : Submodule k V)
  证明: by
  ext v
  rw [mem_direction_iff_eq_vsub (mk'_nonempty _ _)]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    simpa using direction.sub_mem hp₁ hp₂
  · exact fun hv => ⟨v +ᵥ p, vadd_mem_mk' _ hv, p, self_mem_mk' _ _, (vadd_vsub _ _).symm⟩

Depends on / 依赖: _nonempty, direction, direction.sub_mem, mem_direction_iff_eq_vsub, self_mem_mk, sub_mem, vadd_mem_mk, vadd_vsub
-/
theorem direction_mk' (p : P) (direction : Submodule k V) :
    (mk' p direction).direction = direction := by
  ext v
  rw [mem_direction_iff_eq_vsub (mk'_nonempty _ _)]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    simpa using direction.sub_mem hp₁ hp₂
  · exact fun hv => ⟨v +ᵥ p, vadd_mem_mk' _ hv, p, self_mem_mk' _ _, (vadd_vsub _ _).symm⟩

/-- Constructing an affine subspace from a point in a subspace and that subspace's direction
yields the original subspace. -/
@[simp]
/--
theorem `mk'_eq` / 定理 `mk'_eq`

English:
theorem mk'_eq
  given: {s : AffineSubspace k P} {p : P} (hp : p in s)
  statement: mk' p s.direction = s
  proof: ext_of_direction_eq (direction_mk' p s.direction) ⟨p, Set.mem_inter (self_mem_mk' _ _) hp⟩

中文:
定理 mk'_eq
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s)
  结论: mk' p s.direction = s
  证明: ext_of_direction_eq (direction_mk' p s.direction) ⟨p, Set.mem_inter (self_mem_mk' _ _) hp⟩
-/
theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p in s) : mk' p s.direction = s :=
  ext_of_direction_eq (direction_mk' p s.direction) ⟨p, Set.mem_inter (self_mem_mk' _ _) hp⟩

/--
theorem `spanPoints_subset_coe_of_subset_coe` / 定理 `spanPoints_subset_coe_of_subset_coe`

English:
theorem spanPoints_subset_coe_of_subset_coe
  given: {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁)
  proof: by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ in (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s <= s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_o

中文:
定理 spanPoints_subset_coe_of_subset_coe
  条件: {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁)
  证明: by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ in (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s <= s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_o

Depends on / 依赖: Set.mem_of_mem_of_subset, SetLike, SetLike.le_def, SetLike.mem_coe, direction, le_def, mem_coe, mem_of_mem_of_subset, vadd_mem_of_mem_direction, vectorSpan, vectorSpan_mono
-/
theorem spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁) :
    spanPoints k s subseteq s₁ := by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ in (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s <= s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_of_subset hv hs

end AffineSubspace

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

@[simp]
/--
theorem `toAffineSubspace_direction` / 定理 `toAffineSubspace_direction`

English:
theorem toAffineSubspace_direction
  given: (s : Submodule k V)
  statement: s.toAffineSubspace.direction = s
  proof: by
  ext x; simp [← s.toAffineSubspace.vadd_mem_iff_mem_direction _ s.zero_mem]

中文:
定理 toAffineSubspace_direction
  条件: (s : Submodule k V)
  结论: s.toAffineSubspace.direction = s
  证明: by
  ext x; simp [← s.toAffineSubspace.vadd_mem_iff_mem_direction _ s.zero_mem]

Depends on / 依赖: s.toAffineSubspace.vadd_mem_iff_mem_direction, s.zero_mem, toAffineSubspace, vadd_mem_iff_mem_direction, zero_mem
-/
theorem toAffineSubspace_direction (s : Submodule k V) : s.toAffineSubspace.direction = s := by
  ext x; simp [← s.toAffineSubspace.vadd_mem_iff_mem_direction _ s.zero_mem]

end Submodule

section affineSpan

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/--
Definition of `affineSpan` / `affineSpan` 的定义

English:
definition affineSpan
  signature: (s : Set P)
  body: spanPoints k s
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp₃
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂))

中文:
定义 affineSpan
  签名: (s : Set P)
  定义体: spanPoints k s
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp₃
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂))

Depends on / 依赖: spanPoints
-/
def affineSpan (s : Set P) : AffineSubspace k P where
  carrier := spanPoints k s
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp₃
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂))

/--
theorem `coe_affineSpan` / 定理 `coe_affineSpan`

English:
theorem coe_affineSpan
  given: (s : Set P)
  statement: (affineSpan k s : Set P) = spanPoints k s
  proof: rfl

中文:
定理 coe_affineSpan
  条件: (s : Set P)
  结论: (affineSpan k s : Set P) = spanPoints k s
  证明: rfl
-/
theorem coe_affineSpan (s : Set P) : (affineSpan k s : Set P) = spanPoints k s :=
  rfl

/--
lemma `mem_affineSpan_iff_exists` / 引理 `mem_affineSpan_iff_exists`

English:
lemma mem_affineSpan_iff_exists
  given: {p : P} {s : Set P}
  statement: p in affineSpan k s ↔
  proof: Iff.rfl

中文:
引理 mem_affineSpan_iff_exists
  条件: {p : P} {s : Set P}
  结论: p in affineSpan k s ↔
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_affineSpan_iff_exists {p : P} {s : Set P} : p in affineSpan k s ↔
    exists p₁ in s, exists v in vectorSpan k s, p = v +ᵥ p₁ :=
  Iff.rfl

/--
theorem `subset_affineSpan` / 定理 `subset_affineSpan`

English:
theorem subset_affineSpan
  given: (s : Set P)
  statement: s subseteq affineSpan k s
  proof: subset_spanPoints k s

中文:
定理 subset_affineSpan
  条件: (s : Set P)
  结论: s subseteq affineSpan k s
  证明: subset_spanPoints k s

Depends on / 依赖: subset_spanPoints
-/
theorem subset_affineSpan (s : Set P) : s subseteq affineSpan k s :=
  subset_spanPoints k s

/--
theorem `direction_affineSpan` / 定理 `direction_affineSpan`

English:
theorem direction_affineSpan
  given: (s : Set P)
  statement: (affineSpan k s).direction = vectorSpan k s
  proof: by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨p₁, ⟨p₂, hp₂, v₁, hv₁, hp₁⟩, p₃, ⟨p₄, hp₄, v₂, hv₂, hp₃⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hp₁]; rw [hp₃]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]
    exact
      (vectorSpan k s).sub_mem ((vectorSpan k s).ad

中文:
定理 direction_affineSpan
  条件: (s : Set P)
  结论: (affineSpan k s).direction = vectorSpan k s
  证明: by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨p₁, ⟨p₂, hp₂, v₁, hv₁, hp₁⟩, p₃, ⟨p₄, hp₄, v₂, hv₂, hp₃⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hp₁]; rw [hp₃]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]
    exact
      (vectorSpan k s).sub_mem ((vectorSpan k s).ad

Depends on / 依赖: SetLike, SetLike.mem_coe, Submodule, Submodule.span_le, add_mem, le_antisymm, mem_coe, span_le, sub_mem, subset_spanPoints, vadd_vsub_assoc, vectorSpan, vectorSpan_mono, vsub_mem_vectorSpan, vsub_vadd_eq_vsub_sub
-/
theorem direction_affineSpan (s : Set P) : (affineSpan k s).direction = vectorSpan k s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨p₁, ⟨p₂, hp₂, v₁, hv₁, hp₁⟩, p₃, ⟨p₄, hp₄, v₂, hv₂, hp₃⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hp₁]; rw [hp₃]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]
    exact
      (vectorSpan k s).sub_mem ((vectorSpan k s).add_mem hv₁ (vsub_mem_vectorSpan k hp₂ hp₄)) hv₂
  · exact vectorSpan_mono k (subset_spanPoints k s)

/--
theorem `mem_affineSpan` / 定理 `mem_affineSpan`

English:
theorem mem_affineSpan
  given: {p : P} {s : Set P} (hp : p in s)
  statement: p in affineSpan k s
  proof: mem_spanPoints k p s hp

@[simp]

中文:
定理 mem_affineSpan
  条件: {p : P} {s : Set P} (hp : p in s)
  结论: p in affineSpan k s
  证明: mem_spanPoints k p s hp

@[simp]

Depends on / 依赖: mem_spanPoints
-/
theorem mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in affineSpan k s :=
  mem_spanPoints k p s hp

@[simp]
/--
lemma `vectorSpan_add_self` / 引理 `vectorSpan_add_self`

English:
lemma vectorSpan_add_self
  given: (s : Set V)
  statement: (vectorSpan k s : Set V) + s = affineSpan k s
  proof: by
  ext
  simp [mem_add, coe_affineSpan, spanPoints]
  grind

中文:
引理 vectorSpan_add_self
  条件: (s : Set V)
  结论: (vectorSpan k s : Set V) + s = affineSpan k s
  证明: by
  ext
  simp [mem_add, coe_affineSpan, spanPoints]
  grind

Depends on / 依赖: coe_affineSpan, mem_add, spanPoints
-/
lemma vectorSpan_add_self (s : Set V) : (vectorSpan k s : Set V) + s = affineSpan k s := by
  ext
  simp [mem_add, coe_affineSpan, spanPoints]
  grind

variable {k}

/--
theorem `vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan` / 定理 `vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan`

English:
theorem vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
  statement: {s : Set P} {p : P} {v : V}
  proof: vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp hv

中文:
定理 vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
  结论: {s : Set P} {p : P} {v : V}
  证明: vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp hv

Depends on / 依赖: vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan
-/
theorem vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p in affineSpan k s) (hv : v in vectorSpan k s) : v +ᵥ p in affineSpan k s :=
  vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp hv

/--
theorem `vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan` / 定理 `vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan`

English:
theorem vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
  statement: {s : Set P} {p₁ p₂ : P}
  proof: vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂

中文:
定理 vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
  结论: {s : Set P} {p₁ p₂ : P}
  证明: vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂

Depends on / 依赖: vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints
-/
theorem vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ in affineSpan k s) (hp₂ : p₂ in affineSpan k s) : p₁ -ᵥ p₂ in vectorSpan k s :=
  vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂

/--
theorem `affineSpan_le_of_subset_coe` / 定理 `affineSpan_le_of_subset_coe`

English:
theorem affineSpan_le_of_subset_coe
  given: {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁)
  proof: AffineSubspace.spanPoints_subset_coe_of_subset_coe h

中文:
定理 affineSpan_le_of_subset_coe
  条件: {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁)
  证明: AffineSubspace.spanPoints_subset_coe_of_subset_coe h

Depends on / 依赖: AffineSubspace, AffineSubspace.spanPoints_subset_coe_of_subset_coe, spanPoints_subset_coe_of_subset_coe
-/
theorem affineSpan_le_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁) :
    affineSpan k s <= s₁ :=
  AffineSubspace.spanPoints_subset_coe_of_subset_coe h

end affineSpan

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P] {ι : Sort*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (AffineSubspace k P)
  body: fun s₁ s₂ => affineSpan k (s₁ union s₂)
  le_sup_left := fun _ _ =>
    Set.Subset.trans Set.subset_union_left (subset_spanPoints k _)
  le_sup_right := fun _ _ =>
    Set.Subset.trans Set.subset_union_right (subset_spanPoints k _)
  sup_le := fun _ _ _ hs₁ hs₂ => spanPoints_subset_coe_of_subset_coe

中文:
实例 :
  签名: CompleteLattice (AffineSubspace k P)
  定义体: fun s₁ s₂ => affineSpan k (s₁ union s₂)
  le_sup_left := fun _ _ =>
    Set.Subset.trans Set.subset_union_left (subset_spanPoints k _)
  le_sup_right := fun _ _ =>
    Set.Subset.trans Set.subset_union_right (subset_spanPoints k _)
  sup_le := fun _ _ _ hs₁ hs₂ => spanPoints_subset_coe_of_subset_coe

Depends on / 依赖: affineSpan
-/
instance : CompleteLattice (AffineSubspace k P) where
  sup := fun s₁ s₂ => affineSpan k (s₁ union s₂)
  le_sup_left := fun _ _ =>
    Set.Subset.trans Set.subset_union_left (subset_spanPoints k _)
  le_sup_right := fun _ _ =>
    Set.Subset.trans Set.subset_union_right (subset_spanPoints k _)
  sup_le := fun _ _ _ hs₁ hs₂ => spanPoints_subset_coe_of_subset_coe (Set.union_subset hs₁ hs₂)
  inf := fun s₁ s₂ =>
    mk (s₁ inter s₂) fun c _ _ _ hp₁ hp₂ hp₃ =>
      ⟨s₁.smul_vsub_vadd_mem c hp₁.1 hp₂.1 hp₃.1, s₂.smul_vsub_vadd_mem c hp₁.2 hp₂.2 hp₃.2⟩
  inf_le_left := fun _ _ => Set.inter_subset_left
  inf_le_right := fun _ _ => Set.inter_subset_right
  top :=
    { carrier := Set.univ
      smul_vsub_vadd_mem' _ _ _ _ _ _ _ := Set.mem_univ _ }
  le_top := fun _ _ _ => Set.mem_univ _
  bot :=
    { carrier := ∅
      smul_vsub_vadd_mem' _ _ _ _ := False.elim }
  bot_le := fun _ _ => False.elim
  sSup := fun s => affineSpan k (⋃ s' in s, (s' : Set P))
  sInf := fun s =>
    mk (⋂ s' in s, (s' : Set P)) fun c p₁ p₂ p₃ hp₁ hp₂ hp₃ =>
      Set.mem_iInter₂.2 fun s₂ hs₂ => by
        rw [Set.mem_iInter₂] at *
        exact s₂.smul_vsub_vadd_mem c (hp₁ s₂ hs₂) (hp₂ s₂ hs₂) (hp₃ s₂ hs₂)
  isLUB_sSup _ :=
    ⟨fun _ h => Set.Subset.trans (Set.subset_biUnion_of_mem h) (subset_spanPoints k _),
      fun _ h => spanPoints_subset_coe_of_subset_coe (Set.iUnion₂_subset h)⟩
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf
  le_inf := fun _ _ _ => Set.subset_inter

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AffineSubspace k P)
  body: ⟨⊤⟩

中文:
实例 :
  签名: Inhabited (AffineSubspace k P)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (AffineSubspace k P) :=
  ⟨⊤⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: (s₁ s₂ : AffineSubspace k P)
  statement: s₁ <= s₂ ↔ (s₁ : Set P) subseteq s₂
  proof: Iff.rfl

中文:
定理 le_def
  条件: (s₁ s₂ : AffineSubspace k P)
  结论: s₁ <= s₂ ↔ (s₁ : Set P) subseteq s₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ ↔ (s₁ : Set P) subseteq s₂ :=
  Iff.rfl

/--
theorem `le_def'` / 定理 `le_def'`

English:
theorem le_def'
  given: (s₁ s₂ : AffineSubspace k P)
  statement: s₁ <= s₂ ↔ forall p in s₁, p in s₂
  proof: Iff.rfl

中文:
定理 le_def'
  条件: (s₁ s₂ : AffineSubspace k P)
  结论: s₁ <= s₂ ↔ 对任意 p in s₁, p in s₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def' (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ ↔ forall p in s₁, p in s₂ :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: (s₁ s₂ : AffineSubspace k P)
  statement: s₁ < s₂ ↔ (s₁ : Set P) ⊂ s₂
  proof: Iff.rfl

中文:
定理 lt_def
  条件: (s₁ s₂ : AffineSubspace k P)
  结论: s₁ < s₂ ↔ (s₁ : Set P) ⊂ s₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_def (s₁ s₂ : AffineSubspace k P) : s₁ < s₂ ↔ (s₁ : Set P) ⊂ s₂ :=
  Iff.rfl

/--
theorem `not_le_iff_exists` / 定理 `not_le_iff_exists`

English:
theorem not_le_iff_exists
  given: (s₁ s₂ : AffineSubspace k P)
  statement: ¬s₁ <= s₂ ↔ exists p in s₁, p ∉ s₂
  proof: Set.not_subset

中文:
定理 not_le_iff_exists
  条件: (s₁ s₂ : AffineSubspace k P)
  结论: ¬s₁ <= s₂ ↔ 存在 p in s₁, p ∉ s₂
  证明: Set.not_subset

Depends on / 依赖: Set.not_subset, not_subset
-/
theorem not_le_iff_exists (s₁ s₂ : AffineSubspace k P) : ¬s₁ <= s₂ ↔ exists p in s₁, p ∉ s₂ :=
  Set.not_subset

/--
theorem `exists_of_lt` / 定理 `exists_of_lt`

English:
theorem exists_of_lt
  given: {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
  statement: exists p in s₂, p ∉ s₁
  proof: Set.exists_of_ssubset h

中文:
定理 exists_of_lt
  条件: {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
  结论: 存在 p in s₂, p ∉ s₁
  证明: Set.exists_of_ssubset h

Depends on / 依赖: Set.exists_of_ssubset, exists_of_ssubset
-/
theorem exists_of_lt {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂) : exists p in s₂, p ∉ s₁ :=
  Set.exists_of_ssubset h

/--
theorem `lt_iff_le_and_exists` / 定理 `lt_iff_le_and_exists`

English:
theorem lt_iff_le_and_exists
  given: (s₁ s₂ : AffineSubspace k P)
  proof: by
  rw [lt_iff_le_not_ge]; rw [not_le_iff_exists]

中文:
定理 lt_iff_le_and_exists
  条件: (s₁ s₂ : AffineSubspace k P)
  证明: by
  rw [lt_iff_le_not_ge]; rw [not_le_iff_exists]

Depends on / 依赖: lt_iff_le_not_ge, not_le_iff_exists
-/
theorem lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) :
    s₁ < s₂ ↔ s₁ <= s₂ ∧ exists p in s₂, p ∉ s₁ := by
  rw [lt_iff_le_not_ge]; rw [not_le_iff_exists]

/--
theorem `eq_of_direction_eq_of_nonempty_of_le` / 定理 `eq_of_direction_eq_of_nonempty_of_le`

English:
theorem eq_of_direction_eq_of_nonempty_of_le
  statement: {s₁ s₂ : AffineSubspace k P}
  proof: let ⟨p, hp⟩ := hn
  ext_of_direction_eq hd ⟨p, hp, hle hp⟩

中文:
定理 eq_of_direction_eq_of_nonempty_of_le
  结论: {s₁ s₂ : AffineSubspace k P}
  证明: let ⟨p, hp⟩ := hn
  ext_of_direction_eq hd ⟨p, hp, hle hp⟩

Depends on / 依赖: ext_of_direction_eq
-/
theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P}
    (hd : s₁.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ <= s₂) : s₁ = s₂ :=
  let ⟨p, hp⟩ := hn
  ext_of_direction_eq hd ⟨p, hp, hle hp⟩

/--
Instance `nonempty_sup_left` / 实例 `nonempty_sup_left`

English:
instance nonempty_sup_left
  signature: (s₁ s₂ : AffineSubspace k P) [Nonempty s₁]
  body: .map (Set.inclusion <| SetLike.le_def.1 le_sup_left) ‹_›

中文:
实例 nonempty_sup_left
  签名: (s₁ s₂ : AffineSubspace k P) [Nonempty s₁]
  定义体: .map (Set.inclusion <| SetLike.le_def.1 le_sup_left) ‹_›

Depends on / 依赖: Set.inclusion, SetLike, SetLike.le_def, inclusion, le_def, le_sup_left
-/
instance nonempty_sup_left (s₁ s₂ : AffineSubspace k P) [Nonempty s₁] :
    Nonempty (s₁ ⊔ s₂ : AffineSubspace k P) :=
  .map (Set.inclusion <| SetLike.le_def.1 le_sup_left) ‹_›

/--
Instance `nonempty_sup_right` / 实例 `nonempty_sup_right`

English:
instance nonempty_sup_right
  signature: (s₁ s₂ : AffineSubspace k P) [Nonempty s₂]
  body: .map (Set.inclusion <| SetLike.le_def.1 le_sup_right) ‹_›

中文:
实例 nonempty_sup_right
  签名: (s₁ s₂ : AffineSubspace k P) [Nonempty s₂]
  定义体: .map (Set.inclusion <| SetLike.le_def.1 le_sup_right) ‹_›

Depends on / 依赖: Set.inclusion, SetLike, SetLike.le_def, inclusion, le_def, le_sup_right
-/
instance nonempty_sup_right (s₁ s₂ : AffineSubspace k P) [Nonempty s₂] :
    Nonempty (s₁ ⊔ s₂ : AffineSubspace k P) :=
  .map (Set.inclusion <| SetLike.le_def.1 le_sup_right) ‹_›

variable (k V)

/--
theorem `affineSpan_eq_sInf` / 定理 `affineSpan_eq_sInf`

English:
theorem affineSpan_eq_sInf
  given: (s : Set P)
  proof: le_antisymm (affineSpan_le_of_subset_coe <| Set.subset_iInter₂ fun _ => id)
    (sInf_le (subset_spanPoints k _))

中文:
定理 affineSpan_eq_sInf
  条件: (s : Set P)
  证明: le_antisymm (affineSpan_le_of_subset_coe <| Set.subset_iInter₂ fun _ => id)
    (sInf_le (subset_spanPoints k _))

Depends on / 依赖: Set.subset_iInter, affineSpan_le_of_subset_coe, le_antisymm, sInf_le, subset_spanPoints
-/
theorem affineSpan_eq_sInf (s : Set P) :
    affineSpan k s = sInf { s' : AffineSubspace k P | s subseteq s' } :=
  le_antisymm (affineSpan_le_of_subset_coe <| Set.subset_iInter₂ fun _ => id)
    (sInf_le (subset_spanPoints k _))

variable (P)

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (affineSpan k) ((↑) : AffineSubspace k P -> Set P) where
  body: affineSpan k s
  gc s₁ _s₂ :=
    ⟨fun h => Set.Subset.trans (subset_spanPoints k s₁) h, affineSpan_le_of_subset_coe⟩
  le_l_u _ := subset_spanPoints k _
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : GaloisInsertion (affineSpan k) ((↑) : AffineSubspace k P -> Set P) where
  定义体: affineSpan k s
  gc s₁ _s₂ :=
    ⟨fun h => Set.Subset.trans (subset_spanPoints k s₁) h, affineSpan_le_of_subset_coe⟩
  le_l_u _ := subset_spanPoints k _
  choice_eq _ _ := rfl
-/
protected def gi : GaloisInsertion (affineSpan k) ((↑) : AffineSubspace k P -> Set P) where
  choice s _ := affineSpan k s
  gc s₁ _s₂ :=
    ⟨fun h => Set.Subset.trans (subset_spanPoints k s₁) h, affineSpan_le_of_subset_coe⟩
  le_l_u _ := subset_spanPoints k _
  choice_eq _ _ := rfl

/-- The span of the empty set is `⊥`. -/
@[simp]
/--
theorem `span_empty` / 定理 `span_empty`

English:
theorem span_empty
  statement: affineSpan k (∅ : Set P) = ⊥
  proof: (AffineSubspace.gi k V P).gc.l_bot

中文:
定理 span_empty
  结论: affineSpan k (∅ : Set P) = ⊥
  证明: (AffineSubspace.gi k V P).gc.l_bot

Depends on / 依赖: AffineSubspace, AffineSubspace.gi, gc.l_bot, l_bot
-/
theorem span_empty : affineSpan k (∅ : Set P) = ⊥ :=
  (AffineSubspace.gi k V P).gc.l_bot

/-- The span of `univ` is `⊤`. -/
@[simp]
/--
theorem `span_univ` / 定理 `span_univ`

English:
theorem span_univ
  statement: affineSpan k (Set.univ : Set P) = ⊤
  proof: eq_top_iff.2 subset_affineSpan k _

中文:
定理 span_univ
  结论: affineSpan k (Set.univ : Set P) = ⊤
  证明: eq_top_iff.2 subset_affineSpan k _

Depends on / 依赖: eq_top_iff, subset_affineSpan
-/
theorem span_univ : affineSpan k (Set.univ : Set P) = ⊤ :=
eq_top_iff.2 subset_affineSpan k _

variable {k V P}

/--
theorem `_root_.affineSpan_le` / 定理 `_root_.affineSpan_le`

English:
theorem _root_.affineSpan_le
  given: {s : Set P} {Q : AffineSubspace k P}
  proof: (AffineSubspace.gi k V P).gc _ _

中文:
定理 _root_.affineSpan_le
  条件: {s : Set P} {Q : AffineSubspace k P}
  证明: (AffineSubspace.gi k V P).gc _ _

Depends on / 依赖: AffineSubspace, AffineSubspace.gi
-/
theorem _root_.affineSpan_le {s : Set P} {Q : AffineSubspace k P} :
    affineSpan k s <= Q ↔ s subseteq (Q : Set P) :=
  (AffineSubspace.gi k V P).gc _ _

variable (k V) {p₁ p₂ : P}

/--
theorem `span_union` / 定理 `span_union`

English:
theorem span_union
  given: (s t : Set P)
  statement: affineSpan k (s union t) = affineSpan k s ⊔ affineSpan k t
  proof: (AffineSubspace.gi k V P).gc.l_sup

中文:
定理 span_union
  条件: (s t : Set P)
  结论: affineSpan k (s union t) = affineSpan k s ⊔ affineSpan k t
  证明: (AffineSubspace.gi k V P).gc.l_sup

Depends on / 依赖: AffineSubspace, AffineSubspace.gi, gc.l_sup, l_sup
-/
theorem span_union (s t : Set P) : affineSpan k (s union t) = affineSpan k s ⊔ affineSpan k t :=
  (AffineSubspace.gi k V P).gc.l_sup

/--
theorem `span_iUnion` / 定理 `span_iUnion`

English:
theorem span_iUnion
  given: {ι : Type*} (s : ι -> Set P)
  proof: (AffineSubspace.gi k V P).gc.l_iSup

中文:
定理 span_iUnion
  条件: {ι : 类型} (s : ι -> Set P)
  证明: (AffineSubspace.gi k V P).gc.l_iSup

Depends on / 依赖: AffineSubspace, AffineSubspace.gi, gc.l_iSup, l_iSup
-/
theorem span_iUnion {ι : Type*} (s : ι -> Set P) :
    affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) :=
  (AffineSubspace.gi k V P).gc.l_iSup

variable (P) in
/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp]
/--
theorem `top_coe` / 定理 `top_coe`

English:
theorem top_coe
  statement: ((⊤ : AffineSubspace k P) : Set P) = Set.univ
  proof: rfl

中文:
定理 top_coe
  结论: ((⊤ : AffineSubspace k P) : Set P) = Set.univ
  证明: rfl
-/
theorem top_coe : ((⊤ : AffineSubspace k P) : Set P) = Set.univ :=
  rfl

/-- All points are in `⊤`. -/
@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (p : P)
  statement: p in (⊤ : AffineSubspace k P)
  proof: Set.mem_univ p

中文:
定理 mem_top
  条件: (p : P)
  结论: p in (⊤ : AffineSubspace k P)
  证明: Set.mem_univ p

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (p : P) : p in (⊤ : AffineSubspace k P) :=
  Set.mem_univ p

/--
lemma `mk'_top` / 引理 `mk'_top`

English:
lemma mk'_top
  given: (p : P)
  statement: mk' p (⊤ : Submodule k V) = ⊤
  proof: by
  ext x
  simp [mem_mk']

中文:
引理 mk'_top
  条件: (p : P)
  结论: mk' p (⊤ : Submodule k V) = ⊤
  证明: by
  ext x
  simp [mem_mk']
-/
@[simp] lemma mk'_top (p : P) : mk' p (⊤ : Submodule k V) = ⊤ := by
  ext x
  simp [mem_mk']

variable (P)

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp]
/--
theorem `direction_top` / 定理 `direction_top`

English:
theorem direction_top
  statement: (⊤ : AffineSubspace k P).direction = ⊤
  proof: by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) in (⊤ : AffineSubspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _)
  rwa [vadd_vsub] at hpv

中文:
定理 direction_top
  结论: (⊤ : AffineSubspace k P).direction = ⊤
  证明: by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) in (⊤ : AffineSubspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _)
  rwa [vadd_vsub] at hpv

Depends on / 依赖: AffineSubspace, S.nonempty, Submodule, Submodule.mem_top, direction, imp_intro, mem_top, nonempty, vadd_vsub, vsub_mem_direction
-/
theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) in (⊤ : AffineSubspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _)
  rwa [vadd_vsub] at hpv

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp]
/--
theorem `bot_coe` / 定理 `bot_coe`

English:
theorem bot_coe
  statement: ((⊥ : AffineSubspace k P) : Set P) = ∅
  proof: rfl

中文:
定理 bot_coe
  结论: ((⊥ : AffineSubspace k P) : Set P) = ∅
  证明: rfl
-/
theorem bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅ :=
  rfl

/--
theorem `bot_ne_top` / 定理 `bot_ne_top`

English:
theorem bot_ne_top
  statement: (⊥ : AffineSubspace k P) != ⊤
  proof: by
  intro contra
  rw [AffineSubspace.ext_iff]; rw [bot_coe]; rw [top_coe] at contra
  exact Set.empty_ne_univ contra

中文:
定理 bot_ne_top
  结论: (⊥ : AffineSubspace k P) != ⊤
  证明: by
  intro contra
  rw [AffineSubspace.ext_iff]; rw [bot_coe]; rw [top_coe] at contra
  exact Set.empty_ne_univ contra

Depends on / 依赖: AffineSubspace, AffineSubspace.ext_iff, Function, Function.isEmpty, Set.empty_ne_univ, bot_coe, contra, empty_ne_univ, ext_iff, h.elim, isEmpty, top_coe
-/
theorem bot_ne_top : (⊥ : AffineSubspace k P) != ⊤ := by
  intro contra
  rw [AffineSubspace.ext_iff]; rw [bot_coe]; rw [top_coe] at contra
  exact Set.empty_ne_univ contra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (AffineSubspace k P)
  body: ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩

中文:
实例 :
  签名: Nontrivial (AffineSubspace k P)
  定义体: ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩

Depends on / 依赖: bot_ne_top
-/
instance : Nontrivial (AffineSubspace k P) :=
  ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩

/--
theorem `nonempty_of_affineSpan_eq_top` / 定理 `nonempty_of_affineSpan_eq_top`

English:
theorem nonempty_of_affineSpan_eq_top
  given: {s : Set P} (h : affineSpan k s = ⊤)
  statement: s.Nonempty
  proof: by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact bot_ne_top k V P h

中文:
定理 nonempty_of_affineSpan_eq_top
  条件: {s : Set P} (h : affineSpan k s = ⊤)
  结论: s.Nonempty
  证明: by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact bot_ne_top k V P h

Depends on / 依赖: AffineSubspace, AffineSubspace.span_empty, Set.nonempty_iff_ne_empty, bot_ne_top, nonempty_iff_ne_empty, span_empty
-/
theorem nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact bot_ne_top k V P h

/--
theorem `vectorSpan_eq_top_of_affineSpan_eq_top` / 定理 `vectorSpan_eq_top_of_affineSpan_eq_top`

English:
theorem vectorSpan_eq_top_of_affineSpan_eq_top
  given: {s : Set P} (h : affineSpan k s = ⊤)
  proof: by rw [← direction_affineSpan, h, direction_top]

中文:
定理 vectorSpan_eq_top_of_affineSpan_eq_top
  条件: {s : Set P} (h : affineSpan k s = ⊤)
  证明: by rw [← direction_affineSpan, h, direction_top]

Depends on / 依赖: direction_affineSpan, direction_top
-/
theorem vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) :
    vectorSpan k s = ⊤ := by rw [← direction_affineSpan, h, direction_top]

/--
theorem `affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty` / 定理 `affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty`

English:
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
  given: {s : Set P} (hs : s.Nonempty)
  proof: by
  refine ⟨vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p in affineSpan k s⟩ := this
    rw [eq_iff_direction_eq_of_mem hp (mem_top k V p)]; rw [direction_affineSpan]; rw [h]; rw [direction_top]
  obtain ⟨x, hx⟩ := hs
  exa

中文:
定理 affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
  条件: {s : Set P} (hs : s.Nonempty)
  证明: by
  refine ⟨vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p in affineSpan k s⟩ := this
    rw [eq_iff_direction_eq_of_mem hp (mem_top k V p)]; rw [direction_affineSpan]; rw [h]; rw [direction_top]
  obtain ⟨x, hx⟩ := hs
  exa

Depends on / 依赖: Nonempty, affineSpan, direction_affineSpan, direction_top, eq_iff_direction_eq_of_mem, mem_affineSpan, mem_top, vectorSpan_eq_top_of_affineSpan_eq_top
-/
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  refine ⟨vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p in affineSpan k s⟩ := this
    rw [eq_iff_direction_eq_of_mem hp (mem_top k V p)]; rw [direction_affineSpan]; rw [h]; rw [direction_top]
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨x, mem_affineSpan k hx⟩⟩

/--
theorem `affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial` / 定理 `affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial`

English:
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial
  given: {s : Set P} [Nontrivial P]
  proof: by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, subsingleton_iff_bot_eq_top, AddTorsor.subsingleton_iff V P, not_subsingleton]
  · rw [affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty k V P hs]

中文:
定理 affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial
  条件: {s : Set P} [Nontrivial P]
  证明: by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, subsingleton_iff_bot_eq_top, AddTorsor.subsingleton_iff V P, not_subsingleton]
  · rw [affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty k V P hs]

Depends on / 依赖: AddTorsor, AddTorsor.subsingleton_iff, affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty, eq_empty_or_nonempty, not_subsingleton, s.eq_empty_or_nonempty, subsingleton_iff, subsingleton_iff_bot_eq_top
-/
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial {s : Set P} [Nontrivial P] :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, subsingleton_iff_bot_eq_top, AddTorsor.subsingleton_iff V P, not_subsingleton]
  · rw [affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty k V P hs]

/--
theorem `card_pos_of_affineSpan_eq_top` / 定理 `card_pos_of_affineSpan_eq_top`

English:
theorem card_pos_of_affineSpan_eq_top
  statement: {ι : Type*} [Fintype ι] {p : ι -> P}
  proof: by
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affineSpan_eq_top k V P h
  exact Fintype.card_pos_iff.mpr ⟨i⟩

中文:
定理 card_pos_of_affineSpan_eq_top
  结论: {ι : 类型} [Fintype ι] {p : ι -> P}
  证明: by
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affineSpan_eq_top k V P h
  exact Fintype.card_pos_iff.mpr ⟨i⟩

Depends on / 依赖: Fintype, Fintype.card_pos_iff.mpr, card_pos_iff, nonempty_of_affineSpan_eq_top
-/
theorem card_pos_of_affineSpan_eq_top {ι : Type*} [Fintype ι] {p : ι -> P}
    (h : affineSpan k (range p) = ⊤) : 0 < Fintype.card ι := by
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affineSpan_eq_top k V P h
  exact Fintype.card_pos_iff.mpr ⟨i⟩

-- An instance with better keys for the context
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (⊤ : AffineSubspace k P)
  body: inferInstanceAs (Nonempty (⊤ : Set P))

中文:
实例 :
  签名: Nonempty (⊤ : AffineSubspace k P)
  定义体: inferInstanceAs (Nonempty (⊤ : Set P))

Depends on / 依赖: Nonempty
-/
instance : Nonempty (⊤ : AffineSubspace k P) := inferInstanceAs (Nonempty (⊤ : Set P))

variable {P}

/--
theorem `notMem_bot` / 定理 `notMem_bot`

English:
theorem notMem_bot
  given: (p : P)
  statement: p ∉ (⊥ : AffineSubspace k P)
  proof: Set.notMem_empty p

中文:
定理 notMem_bot
  条件: (p : P)
  结论: p ∉ (⊥ : AffineSubspace k P)
  证明: Set.notMem_empty p

Depends on / 依赖: Set.notMem_empty, notMem_empty
-/
theorem notMem_bot (p : P) : p ∉ (⊥ : AffineSubspace k P) :=
  Set.notMem_empty p

/--
Instance `isEmpty_bot` / 实例 `isEmpty_bot`

English:
instance isEmpty_bot
  signature: : IsEmpty (⊥ : AffineSubspace k P)
  body: Subtype.isEmpty_of_false fun _ => notMem_bot _ _ _

中文:
实例 isEmpty_bot
  签名: : IsEmpty (⊥ : AffineSubspace k P)
  定义体: Subtype.isEmpty_of_false fun _ => notMem_bot _ _ _

Depends on / 依赖: IsEmpty, IsEmpty.false, Subtype, Subtype.isEmpty_of_false, isEmpty_of_false, notMem_bot
-/
instance isEmpty_bot : IsEmpty (⊥ : AffineSubspace k P) :=
  Subtype.isEmpty_of_false fun _ => notMem_bot _ _ _

variable (P)

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp]
/--
theorem `direction_bot` / 定理 `direction_bot`

English:
theorem direction_bot
  statement: (⊥ : AffineSubspace k P).direction = ⊥
  proof: by
  rw [direction_eq_vectorSpan]; rw [bot_coe]; rw [vectorSpan_def]; rw [vsub_empty]; rw [Submodule.span_empty]

中文:
定理 direction_bot
  结论: (⊥ : AffineSubspace k P).direction = ⊥
  证明: by
  rw [direction_eq_vectorSpan]; rw [bot_coe]; rw [vectorSpan_def]; rw [vsub_empty]; rw [Submodule.span_empty]

Depends on / 依赖: Submodule, Submodule.span_empty, bot_coe, direction_eq_vectorSpan, span_empty, vectorSpan_def, vsub_empty
-/
theorem direction_bot : (⊥ : AffineSubspace k P).direction = ⊥ := by
  rw [direction_eq_vectorSpan]; rw [bot_coe]; rw [vectorSpan_def]; rw [vsub_empty]; rw [Submodule.span_empty]

variable {k V P}

@[simp]
/--
theorem `coe_eq_bot_iff` / 定理 `coe_eq_bot_iff`

English:
theorem coe_eq_bot_iff
  given: (Q : AffineSubspace k P)
  statement: (Q : Set P) = ∅ ↔ Q = ⊥
  proof: coe_injective.eq_iff' (bot_coe _ _ _)

@[simp]

中文:
定理 coe_eq_bot_iff
  条件: (Q : AffineSubspace k P)
  结论: (Q : Set P) = ∅ ↔ Q = ⊥
  证明: coe_injective.eq_iff' (bot_coe _ _ _)

@[simp]

Depends on / 依赖: bot_coe, coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥ :=
  coe_injective.eq_iff' (bot_coe _ _ _)

@[simp]
/--
theorem `coe_eq_univ_iff` / 定理 `coe_eq_univ_iff`

English:
theorem coe_eq_univ_iff
  given: (Q : AffineSubspace k P)
  statement: (Q : Set P) = univ ↔ Q = ⊤
  proof: coe_injective.eq_iff' (top_coe _ _ _)

中文:
定理 coe_eq_univ_iff
  条件: (Q : AffineSubspace k P)
  结论: (Q : Set P) = univ ↔ Q = ⊤
  证明: coe_injective.eq_iff' (top_coe _ _ _)

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff, top_coe
-/
theorem coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = univ ↔ Q = ⊤ :=
  coe_injective.eq_iff' (top_coe _ _ _)

/--
theorem `nonempty_iff_ne_bot` / 定理 `nonempty_iff_ne_bot`

English:
theorem nonempty_iff_ne_bot
  given: (Q : AffineSubspace k P)
  statement: (Q : Set P).Nonempty ↔ Q != ⊥
  proof: by
  rw [nonempty_iff_ne_empty]
  exact not_congr Q.coe_eq_bot_iff

中文:
定理 nonempty_iff_ne_bot
  条件: (Q : AffineSubspace k P)
  结论: (Q : Set P).Nonempty ↔ Q != ⊥
  证明: by
  rw [nonempty_iff_ne_empty]
  exact not_congr Q.coe_eq_bot_iff

Depends on / 依赖: Q.coe_eq_bot_iff, coe_eq_bot_iff, nonempty_iff_ne_empty, not_congr
-/
theorem nonempty_iff_ne_bot (Q : AffineSubspace k P) : (Q : Set P).Nonempty ↔ Q != ⊥ := by
  rw [nonempty_iff_ne_empty]
  exact not_congr Q.coe_eq_bot_iff

/--
theorem `eq_bot_or_nonempty` / 定理 `eq_bot_or_nonempty`

English:
theorem eq_bot_or_nonempty
  given: (Q : AffineSubspace k P)
  statement: Q = ⊥ ∨ (Q : Set P).Nonempty
  proof: by
  rw [nonempty_iff_ne_bot]
  apply eq_or_ne

中文:
定理 eq_bot_or_nonempty
  条件: (Q : AffineSubspace k P)
  结论: Q = ⊥ ∨ (Q : Set P).Nonempty
  证明: by
  rw [nonempty_iff_ne_bot]
  apply eq_or_ne

Depends on / 依赖: eq_or_ne, nonempty_iff_ne_bot
-/
theorem eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty := by
  rw [nonempty_iff_ne_bot]
  apply eq_or_ne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: P] : IsSimpleOrder (AffineSubspace k P) where
  body: by
    rw [← coe_eq_bot_iff]; rw [← coe_eq_univ_iff]
    rcases (s : Set P).eq_empty_or_nonempty with h | h
    · exact .inl h
    · exact .inr h.eq_univ

中文:
实例 [Subsingleton
  签名: P] : IsSimpleOrder (AffineSubspace k P) where
  定义体: by
    rw [← coe_eq_bot_iff]; rw [← coe_eq_univ_iff]
    rcases (s : Set P).eq_empty_or_nonempty with h | h
    · exact .inl h
    · exact .inr h.eq_univ

Depends on / 依赖: coe_eq_bot_iff, coe_eq_univ_iff, eq_empty_or_nonempty, eq_univ, h.eq_univ
-/
instance [Subsingleton P] : IsSimpleOrder (AffineSubspace k P) where
  eq_bot_or_eq_top (s : AffineSubspace k P) := by
    rw [← coe_eq_bot_iff]; rw [← coe_eq_univ_iff]
    rcases (s : Set P).eq_empty_or_nonempty with h | h
    · exact .inl h
    · exact .inr h.eq_univ

/-- A nonempty affine subspace is `⊤` if and only if its direction is `⊤`. -/
@[simp]
/--
theorem `direction_eq_top_iff_of_nonempty` / 定理 `direction_eq_top_iff_of_nonempty`

English:
theorem direction_eq_top_iff_of_nonempty
  given: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  proof: by
  constructor
  · intro hd
    rw [← direction_top k V P] at hd
    refine ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

中文:
定理 direction_eq_top_iff_of_nonempty
  条件: {s : AffineSubspace k P} (h : (s : Set P).Nonempty)
  证明: by
  constructor
  · intro hd
    rw [← direction_top k V P] at hd
    refine ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

Depends on / 依赖: direction_top, ext_of_direction_eq
-/
theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hd
    rw [← direction_top k V P] at hd
    refine ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

/-- The inf of two affine subspaces, coerced to a set, is the intersection of the two sets of
points. -/
@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (s₁ s₂ : AffineSubspace k P)
  statement: (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) inter s₂
  proof: rfl

中文:
定理 coe_inf
  条件: (s₁ s₂ : AffineSubspace k P)
  结论: (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) inter s₂
  证明: rfl

Depends on / 依赖: Subsingleton
-/
theorem coe_inf (s₁ s₂ : AffineSubspace k P) : (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) inter s₂ :=
  rfl

/--
theorem `mem_inf_iff` / 定理 `mem_inf_iff`

English:
theorem mem_inf_iff
  given: (p : P) (s₁ s₂ : AffineSubspace k P)
  statement: p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂
  proof: Iff.rfl

中文:
定理 mem_inf_iff
  条件: (p : P) (s₁ s₂ : AffineSubspace k P)
  结论: p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace k P) : p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂ :=
  Iff.rfl

/--
theorem `direction_inf` / 定理 `direction_inf`

English:
theorem direction_inf
  given: (s₁ s₂ : AffineSubspace k P)
  proof: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    le_inf (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_left) hp)
      (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_right) hp)

中文:
定理 direction_inf
  条件: (s₁ s₂ : AffineSubspace k P)
  证明: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    le_inf (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_left) hp)
      (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_right) hp)

Depends on / 依赖: direction_eq_vectorSpan, inter_subset_left, inter_subset_right, le_inf, sInf_le_sInf, vectorSpan_def, vsub_self_mono
-/
theorem direction_inf (s₁ s₂ : AffineSubspace k P) :
    (s₁ ⊓ s₂).direction <= s₁.direction ⊓ s₂.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    le_inf (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_left) hp)
      (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_right) hp)

/--
theorem `direction_inf_of_mem` / 定理 `direction_inf_of_mem`

English:
theorem direction_inf_of_mem
  given: {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂)
  proof: by
  ext v
  rw [Submodule.mem_inf]; rw [← vadd_mem_iff_mem_direction v h₁]; rw [← vadd_mem_iff_mem_direction v h₂]; rw [←
    vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁]; rw [h₂⟩)]; rw [mem_inf_iff]

中文:
定理 direction_inf_of_mem
  条件: {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂)
  证明: by
  ext v
  rw [Submodule.mem_inf]; rw [← vadd_mem_iff_mem_direction v h₁]; rw [← vadd_mem_iff_mem_direction v h₂]; rw [←
    vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁]; rw [h₂⟩)]; rw [mem_inf_iff]

Depends on / 依赖: Submodule, Submodule.mem_inf, mem_inf, mem_inf_iff, vadd_mem_iff_mem_direction
-/
theorem direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := by
  ext v
  rw [Submodule.mem_inf]; rw [← vadd_mem_iff_mem_direction v h₁]; rw [← vadd_mem_iff_mem_direction v h₂]; rw [←
    vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁]; rw [h₂⟩)]; rw [mem_inf_iff]

/--
theorem `direction_inf_of_mem_inf` / 定理 `direction_inf_of_mem_inf`

English:
theorem direction_inf_of_mem_inf
  given: {s₁ s₂ : AffineSubspace k P} {p : P} (h : p in s₁ ⊓ s₂)
  proof: direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

@[simp, norm_cast]

中文:
定理 direction_inf_of_mem_inf
  条件: {s₁ s₂ : AffineSubspace k P} {p : P} (h : p in s₁ ⊓ s₂)
  证明: direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

@[simp, norm_cast]

Depends on / 依赖: direction_inf_of_mem, mem_inf_iff
-/
theorem direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p in s₁ ⊓ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction :=
  direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (t : Set (AffineSubspace k P))
  proof: rfl

中文:
定理 coe_sInf
  条件: (t : Set (AffineSubspace k P))
  证明: rfl
-/
theorem coe_sInf (t : Set (AffineSubspace k P)) :
    ((sInf t : AffineSubspace k P) : Set P) = ⋂ s in t, s :=
  rfl

/--
theorem `mem_sInf_iff` / 定理 `mem_sInf_iff`

English:
theorem mem_sInf_iff
  given: (p : P) (t : Set (AffineSubspace k P))
  statement: p in sInf t ↔ forall s in t, p in s
  proof: Set.mem_iInter₂

中文:
定理 mem_sInf_iff
  条件: (p : P) (t : Set (AffineSubspace k P))
  结论: p in sInf t ↔ 对任意 s in t, p in s
  证明: Set.mem_iInter₂

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf_iff (p : P) (t : Set (AffineSubspace k P)) : p in sInf t ↔ forall s in t, p in s :=
  Set.mem_iInter₂

/--
theorem `direction_sInf` / 定理 `direction_sInf`

English:
theorem direction_sInf
  given: (t : Set (AffineSubspace k P))
  proof: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
exact le_iInf₂ fun s hs => Submodule.span_mono vsub_self_mono biInter_subset_of_mem hs

中文:
定理 direction_sInf
  条件: (t : Set (AffineSubspace k P))
  证明: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
exact le_iInf₂ fun s hs => Submodule.span_mono vsub_self_mono biInter_subset_of_mem hs

Depends on / 依赖: Submodule, Submodule.span_mono, biInter_subset_of_mem, direction_eq_vectorSpan, span_mono, vectorSpan_def, vsub_self_mono
-/
theorem direction_sInf (t : Set (AffineSubspace k P)) :
    direction (sInf t) <= ⨅ s in t, s.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
exact le_iInf₂ fun s hs => Submodule.span_mono vsub_self_mono biInter_subset_of_mem hs

/--
theorem `direction_sInf_of_mem` / 定理 `direction_sInf_of_mem`

English:
theorem direction_sInf_of_mem
  given: (t : Set (AffineSubspace k P)) (p : P) (h : forall s in t, p in s)
  proof: by
  apply (direction_sInf t).antisymm
  intro v hv
  rw [← vadd_mem_iff_mem_direction v ((mem_sInf_iff p t).mpr h)]; rw [mem_sInf_iff]
  intro s hs
  rw [vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs

中文:
定理 direction_sInf_of_mem
  条件: (t : Set (AffineSubspace k P)) (p : P) (h : 对任意 s in t, p in s)
  证明: by
  apply (direction_sInf t).antisymm
  intro v hv
  rw [← vadd_mem_iff_mem_direction v ((mem_sInf_iff p t).mpr h)]; rw [mem_sInf_iff]
  intro s hs
  rw [vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs

Depends on / 依赖: Submodule, Submodule.mem_iInf, antisymm, direction_sInf, mem_iInf, mem_sInf_iff, vadd_mem_iff_mem_direction
-/
theorem direction_sInf_of_mem (t : Set (AffineSubspace k P)) (p : P) (h : forall s in t, p in s) :
    direction (sInf t) = ⨅ s in t, s.direction := by
  apply (direction_sInf t).antisymm
  intro v hv
  rw [← vadd_mem_iff_mem_direction v ((mem_sInf_iff p t).mpr h)]; rw [mem_sInf_iff]
  intro s hs
  rw [vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs

/--
theorem `direction_sInf_of_mem_sInf` / 定理 `direction_sInf_of_mem_sInf`

English:
theorem direction_sInf_of_mem_sInf
  given: (t : Set (AffineSubspace k P)) (p : P) (h : p in sInf t)
  proof: direction_sInf_of_mem t p (mem_sInf_iff p t).mp h

@[simp, norm_cast]

中文:
定理 direction_sInf_of_mem_sInf
  条件: (t : Set (AffineSubspace k P)) (p : P) (h : p in sInf t)
  证明: direction_sInf_of_mem t p (mem_sInf_iff p t).mp h

@[simp, norm_cast]

Depends on / 依赖: direction_sInf_of_mem, mem_sInf_iff
-/
theorem direction_sInf_of_mem_sInf (t : Set (AffineSubspace k P)) (p : P) (h : p in sInf t) :
    direction (sInf t) = ⨅ s in t, s.direction :=
direction_sInf_of_mem t p (mem_sInf_iff p t).mp h

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: (s : ι -> AffineSubspace k P)
  proof: by
  rw [iInf]; rw [coe_sInf]; rw [Set.biInter_range]

中文:
定理 coe_iInf
  条件: (s : ι -> AffineSubspace k P)
  证明: by
  rw [iInf]; rw [coe_sInf]; rw [Set.biInter_range]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf (s : ι -> AffineSubspace k P) :
    ((iInf s : AffineSubspace k P) : Set P) = ⋂ i, s i := by
  rw [iInf]; rw [coe_sInf]; rw [Set.biInter_range]

/--
theorem `mem_iInf_iff` / 定理 `mem_iInf_iff`

English:
theorem mem_iInf_iff
  given: (s : ι -> AffineSubspace k P) (p : P)
  statement: p in iInf s ↔ forall i, p in s i
  proof: by
  rw [iInf]; rw [mem_sInf_iff]; rw [Set.forall_mem_range]

中文:
定理 mem_iInf_iff
  条件: (s : ι -> AffineSubspace k P) (p : P)
  结论: p in iInf s ↔ 对任意 i, p in s i
  证明: by
  rw [iInf]; rw [mem_sInf_iff]; rw [Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf_iff
-/
theorem mem_iInf_iff (s : ι -> AffineSubspace k P) (p : P) : p in iInf s ↔ forall i, p in s i := by
  rw [iInf]; rw [mem_sInf_iff]; rw [Set.forall_mem_range]

/--
theorem `direction_iInf` / 定理 `direction_iInf`

English:
theorem direction_iInf
  given: (s : ι -> AffineSubspace k P)
  proof: by
  apply (direction_sInf _).trans_eq
  rw [iInf_range]

中文:
定理 direction_iInf
  条件: (s : ι -> AffineSubspace k P)
  证明: by
  apply (direction_sInf _).trans_eq
  rw [iInf_range]

Depends on / 依赖: direction_sInf, iInf_range, trans_eq
-/
theorem direction_iInf (s : ι -> AffineSubspace k P) :
    (iInf s).direction <= ⨅ i, (s i).direction := by
  apply (direction_sInf _).trans_eq
  rw [iInf_range]

/--
theorem `direction_iInf_of_mem` / 定理 `direction_iInf_of_mem`

English:
theorem direction_iInf_of_mem
  given: (s : ι -> AffineSubspace k P) (p : P) (h : forall i, p in s i)
  proof: by
  rw [iInf]; rw [direction_sInf_of_mem _ p ?_]; rw [iInf_range]
  rwa [Set.forall_mem_range]

中文:
定理 direction_iInf_of_mem
  条件: (s : ι -> AffineSubspace k P) (p : P) (h : 对任意 i, p in s i)
  证明: by
  rw [iInf]; rw [direction_sInf_of_mem _ p ?_]; rw [iInf_range]
  rwa [Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, direction_sInf_of_mem, forall_mem_range, iInf_range
-/
theorem direction_iInf_of_mem (s : ι -> AffineSubspace k P) (p : P) (h : forall i, p in s i) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf]; rw [direction_sInf_of_mem _ p ?_]; rw [iInf_range]
  rwa [Set.forall_mem_range]

/--
theorem `direction_iInf_of_mem_iInf` / 定理 `direction_iInf_of_mem_iInf`

English:
theorem direction_iInf_of_mem_iInf
  given: (s : ι -> AffineSubspace k P) (p : P) (h : p in iInf s)
  proof: by
  rw [iInf]; rw [direction_sInf_of_mem_sInf _ p h]; rw [iInf_range]

中文:
定理 direction_iInf_of_mem_iInf
  条件: (s : ι -> AffineSubspace k P) (p : P) (h : p in iInf s)
  证明: by
  rw [iInf]; rw [direction_sInf_of_mem_sInf _ p h]; rw [iInf_range]

Depends on / 依赖: direction_sInf_of_mem_sInf, iInf_range
-/
theorem direction_iInf_of_mem_iInf (s : ι -> AffineSubspace k P) (p : P) (h : p in iInf s) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf]; rw [direction_sInf_of_mem_sInf _ p h]; rw [iInf_range]

/--
theorem `direction_le` / 定理 `direction_le`

English:
theorem direction_le
  given: {s₁ s₂ : AffineSubspace k P} (h : s₁ <= s₂)
  statement: s₁.direction <= s₂.direction
  proof: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

中文:
定理 direction_le
  条件: {s₁ s₂ : AffineSubspace k P} (h : s₁ <= s₂)
  结论: s₁.direction <= s₂.direction
  证明: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

Depends on / 依赖: direction_eq_vectorSpan, vectorSpan_def, vectorSpan_mono
-/
theorem direction_le {s₁ s₂ : AffineSubspace k P} (h : s₁ <= s₂) : s₁.direction <= s₂.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

/--
theorem `sup_direction_le` / 定理 `sup_direction_le`

English:
theorem sup_direction_le
  given: (s₁ s₂ : AffineSubspace k P)
  proof: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    sup_le
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s₁ <= s₁ ⊔ s₂)) hp)
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s₂ <= s₁ ⊔ s₂)) hp)

中文:
定理 sup_direction_le
  条件: (s₁ s₂ : AffineSubspace k P)
  证明: by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    sup_le
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s₁ <= s₁ ⊔ s₂)) hp)
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s₂ <= s₁ ⊔ s₂)) hp)

Depends on / 依赖: Set.Subset.trans, Subset, direction_eq_vectorSpan, le_sup_left, le_sup_right, sInf_le_sInf, sup_le, vectorSpan_def, vsub_self_mono
-/
theorem sup_direction_le (s₁ s₂ : AffineSubspace k P) :
    s₁.direction ⊔ s₂.direction <= (s₁ ⊔ s₂).direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    sup_le
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s₁ <= s₁ ⊔ s₂)) hp)
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s₂ <= s₁ ⊔ s₂)) hp)

/--
theorem `sup_direction_lt_of_nonempty_of_inter_empty` / 定理 `sup_direction_lt_of_nonempty_of_inter_empty`

English:
theorem sup_direction_lt_of_nonempty_of_inter_empty
  statement: {s₁ s₂ : AffineSubspace k P}
  proof: by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    vsub_mem_direction ((le_sup_right : s₂ <= s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ <= s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, 

中文:
定理 sup_direction_lt_of_nonempty_of_inter_empty
  结论: {s₁ s₂ : AffineSubspace k P}
  证明: by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    vsub_mem_direction ((le_sup_right : s₂ <= s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ <= s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, 

Depends on / 依赖: SetLike, SetLike.lt_iff_le_and_exists, Submodule, Submodule.mem_sup, add_assoc, add_comm, le_sup_left, le_sup_right, lt_iff_le_and_exists, mem_sup, neg_neg, neg_vsub_eq_vsub_rev, sub_eq_add_neg, sub_eq_zero, sup_direction_le, vadd_vsub_assoc, vsub_mem_direction, vsub_vadd_eq_vsub_sub
-/
theorem sup_direction_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁ inter s₂ : Set P) = ∅) :
    s₁.direction ⊔ s₂.direction < (s₁ ⊔ s₂).direction := by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    vsub_mem_direction ((le_sup_right : s₂ <= s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ <= s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, hv₁v₂⟩
  rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev]; rw [add_comm v₁]; rw [add_assoc]; rw [←
    vadd_vsub_assoc]; rw [← neg_neg v₂]; rw [add_comm]; rw [← sub_eq_add_neg]; rw [← vsub_vadd_eq_vsub_sub]; rw [vsub_eq_zero_iff_eq] at hv₁v₂
  refine Set.Nonempty.ne_empty ?_ he
  use v₁ +ᵥ p₁, vadd_mem_of_mem_direction hv₁ hp₁
  rw [hv₁v₂]
  exact vadd_mem_of_mem_direction (Submodule.neg_mem _ hv₂) hp₂

/--
theorem `inter_nonempty_of_nonempty_of_sup_direction_eq_top` / 定理 `inter_nonempty_of_nonempty_of_sup_direction_eq_top`

English:
theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top
  statement: {s₁ s₂ : AffineSubspace k P}
  proof: by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

中文:
定理 inter_nonempty_of_nonempty_of_sup_direction_eq_top
  结论: {s₁ s₂ : AffineSubspace k P}
  证明: by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

Depends on / 依赖: Set.not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty, not_top_lt, sup_direction_lt_of_nonempty_of_inter_empty
-/
theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : s₁.direction ⊔ s₂.direction = ⊤) : ((s₁ : Set P) inter s₂).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

/--
theorem `inter_eq_singleton_of_nonempty_of_isCompl` / 定理 `inter_eq_singleton_of_nonempty_of_isCompl`

English:
theorem inter_eq_singleton_of_nonempty_of_isCompl
  statement: {s₁ s₂ : AffineSubspace k P}
  proof: by
  obtain ⟨p, hp⟩ := inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p in s₁.direction ⊓ s₂.direction :=
      ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩
    

中文:
定理 inter_eq_singleton_of_nonempty_of_isCompl
  结论: {s₁ s₂ : AffineSubspace k P}
  证明: by
  obtain ⟨p, hp⟩ := inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p in s₁.direction ⊓ s₂.direction :=
      ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩
    

Depends on / 依赖: Nonempty, Nontrivial, Nontrivial.to_nonempty, Set.mem_singleton_iff, Submodule, Submodule.mem_bot, direction, h.symm, hd.inf_eq_bot, hd.sup_eq_top, inf_eq_bot, inter_nonempty_of_nonempty_of_sup_direction_eq_top, mem_bot, mem_singleton_iff, sup_eq_top, to_nonempty, vsub_eq_zero_iff_eq, vsub_mem_direction
-/
theorem inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : IsCompl s₁.direction s₂.direction) : exists p, (s₁ : Set P) inter s₂ = {p} := by
  obtain ⟨p, hp⟩ := inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p in s₁.direction ⊓ s₂.direction :=
      ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩
    rwa [hd.inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp
  · exact fun h => h.symm ▸ hp

/-- Coercing a subspace to a set then taking the affine span produces the original subspace. -/
@[simp]
/--
theorem `affineSpan_coe` / 定理 `affineSpan_coe`

English:
theorem affineSpan_coe
  given: (s : AffineSubspace k P)
  statement: affineSpan k (s : Set P) = s
  proof: by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact vadd_mem_of_mem_direction hv hp₁

@[simp, gcongr]

中文:
定理 affineSpan_coe
  条件: (s : AffineSubspace k P)
  结论: affineSpan k (s : Set P) = s
  证明: by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact vadd_mem_of_mem_direction hv hp₁

@[simp, gcongr]

Depends on / 依赖: le_antisymm, subset_affineSpan, vadd_mem_of_mem_direction
-/
theorem affineSpan_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s := by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact vadd_mem_of_mem_direction hv hp₁

@[simp, gcongr]
/--
theorem `mk'_le_mk'_iff` / 定理 `mk'_le_mk'_iff`

English:
theorem mk'_le_mk'_iff
  given: (p : P) {d₁ d₂ : Submodule k V}
  statement: mk' p d₁ <= mk' p d₂ ↔ d₁ <= d₂
  proof: by
  simp_rw [SetLike.le_def, mem_mk']
  refine ⟨fun h x hx => ?_, fun h x hx => h hx⟩
  simpa using h (show (x +ᵥ p) -ᵥ p in d₁ by simpa using hx)

中文:
定理 mk'_le_mk'_iff
  条件: (p : P) {d₁ d₂ : Submodule k V}
  结论: mk' p d₁ <= mk' p d₂ ↔ d₁ <= d₂
  证明: by
  simp_rw [SetLike.le_def, mem_mk']
  refine ⟨fun h x hx => ?_, fun h x hx => h hx⟩
  simpa using h (show (x +ᵥ p) -ᵥ p in d₁ by simpa using hx)
-/
theorem mk'_le_mk'_iff (p : P) {d₁ d₂ : Submodule k V} : mk' p d₁ <= mk' p d₂ ↔ d₁ <= d₂ := by
  simp_rw [SetLike.le_def, mem_mk']
  refine ⟨fun h x hx => ?_, fun h x hx => h hx⟩
  simpa using h (show (x +ᵥ p) -ᵥ p in d₁ by simpa using hx)

/--
theorem `mk'_strictMono` / 定理 `mk'_strictMono`

English:
theorem mk'_strictMono
  given: (p : P)
  statement: StrictMono (mk' p (k := k))
  proof: strictMono_of_le_iff_le (fun _ _ => (mk'_le_mk'_iff p).symm)

中文:
定理 mk'_strictMono
  条件: (p : P)
  结论: StrictMono (mk' p (k := k))
  证明: strictMono_of_le_iff_le (fun _ _ => (mk'_le_mk'_iff p).symm)
-/
theorem mk'_strictMono (p : P) : StrictMono (mk' p (k := k)) :=
  strictMono_of_le_iff_le (fun _ _ => (mk'_le_mk'_iff p).symm)

end AffineSubspace

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {ι : Type*}

open AffineSubspace

section

variable {s : Set P}

/--
theorem `affineSpan_nonempty` / 定理 `affineSpan_nonempty`

English:
theorem affineSpan_nonempty
  statement: (affineSpan k s : Set P).Nonempty ↔ s.Nonempty
  proof: spanPoints_nonempty k s

alias ⟨_, _root_.Set.Nonempty.affineSpan⟩ := affineSpan_nonempty

中文:
定理 affineSpan_nonempty
  结论: (affineSpan k s : Set P).Nonempty ↔ s.Nonempty
  证明: spanPoints_nonempty k s

alias ⟨_, _root_.Set.Nonempty.affineSpan⟩ := affineSpan_nonempty

Depends on / 依赖: spanPoints_nonempty
-/
theorem affineSpan_nonempty : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty :=
  spanPoints_nonempty k s

alias ⟨_, _root_.Set.Nonempty.affineSpan⟩ := affineSpan_nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: s] : Nonempty (affineSpan k s)
  body: ((nonempty_coe_sort.1 ‹_›).affineSpan _).to_subtype

中文:
实例 [Nonempty
  签名: s] : Nonempty (affineSpan k s)
  定义体: ((nonempty_coe_sort.1 ‹_›).affineSpan _).to_subtype

Depends on / 依赖: affineSpan, nonempty_coe_sort, to_subtype
-/
instance [Nonempty s] : Nonempty (affineSpan k s) :=
  ((nonempty_coe_sort.1 ‹_›).affineSpan _).to_subtype

/-- The affine span of a set is `⊥` if and only if that set is empty. -/
@[simp]
/--
theorem `affineSpan_eq_bot` / 定理 `affineSpan_eq_bot`

English:
theorem affineSpan_eq_bot
  statement: affineSpan k s = ⊥ ↔ s = ∅
  proof: by
  rw [← not_iff_not]; rw [← Ne]; rw [← Ne]; rw [← nonempty_iff_ne_bot]; rw [affineSpan_nonempty]; rw [nonempty_iff_ne_empty]

@[simp]

中文:
定理 affineSpan_eq_bot
  结论: affineSpan k s = ⊥ ↔ s = ∅
  证明: by
  rw [← not_iff_not]; rw [← Ne]; rw [← Ne]; rw [← nonempty_iff_ne_bot]; rw [affineSpan_nonempty]; rw [nonempty_iff_ne_empty]

@[simp]

Depends on / 依赖: affineSpan_nonempty, nonempty_iff_ne_bot, nonempty_iff_ne_empty, not_iff_not
-/
theorem affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅ := by
  rw [← not_iff_not]; rw [← Ne]; rw [← Ne]; rw [← nonempty_iff_ne_bot]; rw [affineSpan_nonempty]; rw [nonempty_iff_ne_empty]

@[simp]
/--
theorem `bot_lt_affineSpan` / 定理 `bot_lt_affineSpan`

English:
theorem bot_lt_affineSpan
  statement: ⊥ < affineSpan k s ↔ s.Nonempty
  proof: by
  rw [bot_lt_iff_ne_bot]; rw [nonempty_iff_ne_empty]
  exact (affineSpan_eq_bot _).not

@[simp]

中文:
定理 bot_lt_affineSpan
  结论: ⊥ < affineSpan k s ↔ s.Nonempty
  证明: by
  rw [bot_lt_iff_ne_bot]; rw [nonempty_iff_ne_empty]
  exact (affineSpan_eq_bot _).not

@[simp]

Depends on / 依赖: affineSpan_eq_bot, bot_lt_iff_ne_bot, nonempty_iff_ne_empty
-/
theorem bot_lt_affineSpan : ⊥ < affineSpan k s ↔ s.Nonempty := by
  rw [bot_lt_iff_ne_bot]; rw [nonempty_iff_ne_empty]
  exact (affineSpan_eq_bot _).not

@[simp]
/--
lemma `affineSpan_eq_top_iff_nonempty_of_subsingleton` / 引理 `affineSpan_eq_top_iff_nonempty_of_subsingleton`

English:
lemma affineSpan_eq_top_iff_nonempty_of_subsingleton
  given: [Subsingleton P]
  proof: by
  rw [← bot_lt_affineSpan k]; rw [IsSimpleOrder.bot_lt_iff_eq_top]

中文:
引理 affineSpan_eq_top_iff_nonempty_of_subsingleton
  条件: [Subsingleton P]
  证明: by
  rw [← bot_lt_affineSpan k]; rw [IsSimpleOrder.bot_lt_iff_eq_top]

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.bot_lt_iff_eq_top, bot_lt_affineSpan, bot_lt_iff_eq_top
-/
lemma affineSpan_eq_top_iff_nonempty_of_subsingleton [Subsingleton P] :
    affineSpan k s = ⊤ ↔ s.Nonempty := by
  rw [← bot_lt_affineSpan k]; rw [IsSimpleOrder.bot_lt_iff_eq_top]

end

variable {k}

/-- An induction principle for span membership. If `p` holds for all elements of `s` and is
preserved under certain affine combinations, then `p` holds for all elements of the span of `s`. -/
@[elab_as_elim]
/--
theorem `affineSpan_induction` / 定理 `affineSpan_induction`

English:
theorem affineSpan_induction
  statement: {x : P} {s : Set P} {p : P -> Prop} (h : x in affineSpan k s)
  proof: (affineSpan_le (Q := ⟨{x | p x}, smul_vsub_vadd⟩)).mpr mem h

中文:
定理 affineSpan_induction
  结论: {x : P} {s : Set P} {p : P -> 命题} (h : x in affineSpan k s)
  证明: (affineSpan_le (Q := ⟨{x | p x}, smul_vsub_vadd⟩)).mpr mem h

Depends on / 依赖: affineSpan_le, smul_vsub_vadd
-/
theorem affineSpan_induction {x : P} {s : Set P} {p : P -> Prop} (h : x in affineSpan k s)
    (mem : forall x : P, x in s -> p x)
    (smul_vsub_vadd : forall (c : k) (u v w : P), p u -> p v -> p w -> p (c • (u -ᵥ v) +ᵥ w)) : p x :=
  (affineSpan_le (Q := ⟨{x | p x}, smul_vsub_vadd⟩)).mpr mem h

/-- A dependent version of `affineSpan_induction`. -/
@[elab_as_elim]
/--
theorem `affineSpan_induction'` / 定理 `affineSpan_induction'`

English:
theorem affineSpan_induction'
  statement: {s : Set P} {p : forall x, x in affineSpan k s -> Prop}
  proof: by
  suffices exists (hx : x in affineSpan k s), p x hx from this.elim fun hx hc => hc
  -- TODO: `induction h using affineSpan_induction` gives the error:
  -- extra targets for '@affineSpan_induction'
  -- It seems that the `induction` tactic has decided to ignore the clause
  -- `using affineSpan

中文:
定理 affineSpan_induction'
  结论: {s : Set P} {p : 对任意 x, x in affineSpan k s -> 命题}
  证明: by
  suffices exists (hx : x in affineSpan k s), p x hx from this.elim fun hx hc => hc
  -- TODO: `induction h using affineSpan_induction` gives the error:
  -- extra targets for '@affineSpan_induction'
  -- It seems that the `induction` tactic has decided to ignore the clause
  -- `using affineSpan

Depends on / 依赖: affineSpan, this.elim
-/
theorem affineSpan_induction' {s : Set P} {p : forall x, x in affineSpan k s -> Prop}
    (mem : forall (y) (hys : y in s), p y (subset_affineSpan k _ hys))
    (smul_vsub_vadd : forall (c : k) (u hu v hv w hw), p u hu -> p v hv -> p w hw ->
      p (c • (u -ᵥ v) +ᵥ w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw))
    {x : P} (h : x in affineSpan k s) : p x h := by
  suffices exists (hx : x in affineSpan k s), p x hx from this.elim fun hx hc => hc
  -- TODO: `induction h using affineSpan_induction` gives the error:
  -- extra targets for '@affineSpan_induction'
  -- It seems that the `induction` tactic has decided to ignore the clause
  -- `using affineSpan_induction` and use `Exists.rec` instead.
  refine affineSpan_induction h ?mem ?smul_vsub_vadd
  · exact fun y hy => ⟨subset_affineSpan _ _ hy, mem y hy⟩
  · exact fun c u v w hu hv hw =>
      hu.elim fun hu' hu => hv.elim fun hv' hv => hw.elim fun hw' hw =>
        ⟨AffineSubspace.smul_vsub_vadd_mem _ _ hu' hv' hw',
              smul_vsub_vadd _ _ _ _ _ _ _ hu hv hw⟩

variable (k)

/--
theorem `vsub_mem_vectorSpan_pair` / 定理 `vsub_mem_vectorSpan_pair`

English:
theorem vsub_mem_vectorSpan_pair
  given: (p₁ p₂ : P)
  statement: p₁ -ᵥ p₂ in vectorSpan k ({p₁, p₂} : Set P)
  proof: vsub_mem_vectorSpan _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

中文:
定理 vsub_mem_vectorSpan_pair
  条件: (p₁ p₂ : P)
  结论: p₁ -ᵥ p₂ in vectorSpan k ({p₁, p₂} : Set P)
  证明: vsub_mem_vectorSpan _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

Depends on / 依赖: Set.mem_insert, Set.mem_insert_of_mem, Set.mem_singleton, mem_insert, mem_insert_of_mem, mem_singleton, vsub_mem_vectorSpan
-/
theorem vsub_mem_vectorSpan_pair (p₁ p₂ : P) : p₁ -ᵥ p₂ in vectorSpan k ({p₁, p₂} : Set P) :=
  vsub_mem_vectorSpan _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/--
theorem `vsub_rev_mem_vectorSpan_pair` / 定理 `vsub_rev_mem_vectorSpan_pair`

English:
theorem vsub_rev_mem_vectorSpan_pair
  given: (p₁ p₂ : P)
  statement: p₂ -ᵥ p₁ in vectorSpan k ({p₁, p₂} : Set P)
  proof: vsub_mem_vectorSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (Set.mem_insert _ _)

中文:
定理 vsub_rev_mem_vectorSpan_pair
  条件: (p₁ p₂ : P)
  结论: p₂ -ᵥ p₁ in vectorSpan k ({p₁, p₂} : Set P)
  证明: vsub_mem_vectorSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (Set.mem_insert _ _)

Depends on / 依赖: Set.mem_insert, Set.mem_insert_of_mem, Set.mem_singleton, mem_insert, mem_insert_of_mem, mem_singleton, vsub_mem_vectorSpan
-/
theorem vsub_rev_mem_vectorSpan_pair (p₁ p₂ : P) : p₂ -ᵥ p₁ in vectorSpan k ({p₁, p₂} : Set P) :=
  vsub_mem_vectorSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (Set.mem_insert _ _)

variable {k}

/--
theorem `smul_vsub_mem_vectorSpan_pair` / 定理 `smul_vsub_mem_vectorSpan_pair`

English:
theorem smul_vsub_mem_vectorSpan_pair
  given: (r : k) (p₁ p₂ : P)
  proof: Submodule.smul_mem _ _ (vsub_mem_vectorSpan_pair k p₁ p₂)

中文:
定理 smul_vsub_mem_vectorSpan_pair
  条件: (r : k) (p₁ p₂ : P)
  证明: Submodule.smul_mem _ _ (vsub_mem_vectorSpan_pair k p₁ p₂)

Depends on / 依赖: Equiv.equivPEmpty, Equiv.punitOfNonemptyOfSubsingleton, Submodule, Submodule.smul_mem, Subsingleton, equivPEmpty, isEmpty_or_nonempty, punitOfNonemptyOfSubsingleton, small_map, small_subsingleton, smul_mem, vsub_mem_vectorSpan_pair
-/
theorem smul_vsub_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₁ -ᵥ p₂) in vectorSpan k ({p₁, p₂} : Set P) :=
  Submodule.smul_mem _ _ (vsub_mem_vectorSpan_pair k p₁ p₂)

/--
theorem `smul_vsub_rev_mem_vectorSpan_pair` / 定理 `smul_vsub_rev_mem_vectorSpan_pair`

English:
theorem smul_vsub_rev_mem_vectorSpan_pair
  given: (r : k) (p₁ p₂ : P)
  proof: Submodule.smul_mem _ _ (vsub_rev_mem_vectorSpan_pair k p₁ p₂)

中文:
定理 smul_vsub_rev_mem_vectorSpan_pair
  条件: (r : k) (p₁ p₂ : P)
  证明: Submodule.smul_mem _ _ (vsub_rev_mem_vectorSpan_pair k p₁ p₂)

Depends on / 依赖: Submodule, Submodule.smul_mem, smul_mem, vsub_rev_mem_vectorSpan_pair
-/
theorem smul_vsub_rev_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) in vectorSpan k ({p₁, p₂} : Set P) :=
  Submodule.smul_mem _ _ (vsub_rev_mem_vectorSpan_pair k p₁ p₂)

variable (k)

/-- The line between two points, as an affine subspace. -/
notation3 "line[" k ", " p₁ ", " p₂ "]" =>
  affineSpan k (insert p₁ (@singleton _ _ Set.instSingletonSet p₂))

/--
theorem `left_mem_affineSpan_pair` / 定理 `left_mem_affineSpan_pair`

English:
theorem left_mem_affineSpan_pair
  given: (p₁ p₂ : P)
  statement: p₁ in line[k, p₁, p₂]
  proof: mem_affineSpan _ (Set.mem_insert _ _)

中文:
定理 left_mem_affineSpan_pair
  条件: (p₁ p₂ : P)
  结论: p₁ in line[k, p₁, p₂]
  证明: mem_affineSpan _ (Set.mem_insert _ _)

Depends on / 依赖: Set.mem_insert, mem_affineSpan, mem_insert
-/
theorem left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in line[k, p₁, p₂] :=
  mem_affineSpan _ (Set.mem_insert _ _)

/--
theorem `right_mem_affineSpan_pair` / 定理 `right_mem_affineSpan_pair`

English:
theorem right_mem_affineSpan_pair
  given: (p₁ p₂ : P)
  statement: p₂ in line[k, p₁, p₂]
  proof: mem_affineSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

中文:
定理 right_mem_affineSpan_pair
  条件: (p₁ p₂ : P)
  结论: p₂ in line[k, p₁, p₂]
  证明: mem_affineSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

Depends on / 依赖: Set.mem_insert_of_mem, Set.mem_singleton, mem_affineSpan, mem_insert_of_mem, mem_singleton
-/
theorem right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in line[k, p₁, p₂] :=
  mem_affineSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable {k}

/--
theorem `affineSpan_pair_le_of_mem_of_mem` / 定理 `affineSpan_pair_le_of_mem_of_mem`

English:
theorem affineSpan_pair_le_of_mem_of_mem
  statement: {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s)
  proof: by
  rw [affineSpan_le]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨hp₁, hp₂⟩

中文:
定理 affineSpan_pair_le_of_mem_of_mem
  结论: {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s)
  证明: by
  rw [affineSpan_le]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨hp₁, hp₂⟩

Depends on / 依赖: Set.insert_subset_iff, Set.singleton_subset_iff, affineSpan_le, insert_subset_iff, singleton_subset_iff
-/
theorem affineSpan_pair_le_of_mem_of_mem {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) : line[k, p₁, p₂] <= s := by
  rw [affineSpan_le]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨hp₁, hp₂⟩

/--
theorem `affineSpan_pair_le_of_left_mem` / 定理 `affineSpan_pair_le_of_left_mem`

English:
theorem affineSpan_pair_le_of_left_mem
  given: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  proof: affineSpan_pair_le_of_mem_of_mem h (right_mem_affineSpan_pair _ _ _)

中文:
定理 affineSpan_pair_le_of_left_mem
  条件: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  证明: affineSpan_pair_le_of_mem_of_mem h (right_mem_affineSpan_pair _ _ _)

Depends on / 依赖: affineSpan_pair_le_of_mem_of_mem, right_mem_affineSpan_pair
-/
theorem affineSpan_pair_le_of_left_mem {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) :
    line[k, p₁, p₃] <= line[k, p₂, p₃] :=
  affineSpan_pair_le_of_mem_of_mem h (right_mem_affineSpan_pair _ _ _)

/--
theorem `affineSpan_pair_le_of_right_mem` / 定理 `affineSpan_pair_le_of_right_mem`

English:
theorem affineSpan_pair_le_of_right_mem
  given: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  proof: affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) h

中文:
定理 affineSpan_pair_le_of_right_mem
  条件: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  证明: affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) h

Depends on / 依赖: affineSpan_pair_le_of_mem_of_mem, left_mem_affineSpan_pair
-/
theorem affineSpan_pair_le_of_right_mem {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) :
    line[k, p₂, p₁] <= line[k, p₂, p₃] :=
  affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) h

variable (k)

/-- `affineSpan` is monotone. -/
@[gcongr, mono]
/--
theorem `affineSpan_mono` / 定理 `affineSpan_mono`

English:
theorem affineSpan_mono
  given: {s₁ s₂ : Set P} (h : s₁ subseteq s₂)
  statement: affineSpan k s₁ <= affineSpan k s₂
  proof: affineSpan_le_of_subset_coe (Set.Subset.trans h (subset_affineSpan k _))

中文:
定理 affineSpan_mono
  条件: {s₁ s₂ : Set P} (h : s₁ subseteq s₂)
  结论: affineSpan k s₁ <= affineSpan k s₂
  证明: affineSpan_le_of_subset_coe (Set.Subset.trans h (subset_affineSpan k _))

Depends on / 依赖: Set.Subset.trans, Subset, affineSpan_le_of_subset_coe, subset_affineSpan
-/
theorem affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : affineSpan k s₁ <= affineSpan k s₂ :=
  affineSpan_le_of_subset_coe (Set.Subset.trans h (subset_affineSpan k _))

/--
theorem `affineSpan_insert_affineSpan` / 定理 `affineSpan_insert_affineSpan`

English:
theorem affineSpan_insert_affineSpan
  given: (p : P) (ps : Set P)
  proof: by
  rw [Set.insert_eq]; rw [Set.insert_eq]; rw [span_union]; rw [span_union]; rw [affineSpan_coe]

中文:
定理 affineSpan_insert_affineSpan
  条件: (p : P) (ps : Set P)
  证明: by
  rw [Set.insert_eq]; rw [Set.insert_eq]; rw [span_union]; rw [span_union]; rw [affineSpan_coe]

Depends on / 依赖: Set.insert_eq, affineSpan_coe, insert_eq, span_union
-/
theorem affineSpan_insert_affineSpan (p : P) (ps : Set P) :
    affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (insert p ps) := by
  rw [Set.insert_eq]; rw [Set.insert_eq]; rw [span_union]; rw [span_union]; rw [affineSpan_coe]

/--
theorem `affineSpan_insert_eq_affineSpan` / 定理 `affineSpan_insert_eq_affineSpan`

English:
theorem affineSpan_insert_eq_affineSpan
  given: {p : P} {ps : Set P} (h : p in affineSpan k ps)
  proof: by
  rw [← mem_coe] at h
  rw [← affineSpan_insert_affineSpan]; rw [Set.insert_eq_of_mem h]; rw [affineSpan_coe]

中文:
定理 affineSpan_insert_eq_affineSpan
  条件: {p : P} {ps : Set P} (h : p in affineSpan k ps)
  证明: by
  rw [← mem_coe] at h
  rw [← affineSpan_insert_affineSpan]; rw [Set.insert_eq_of_mem h]; rw [affineSpan_coe]

Depends on / 依赖: Set.insert_eq_of_mem, affineSpan_coe, affineSpan_insert_affineSpan, insert_eq_of_mem, mem_coe
-/
theorem affineSpan_insert_eq_affineSpan {p : P} {ps : Set P} (h : p in affineSpan k ps) :
    affineSpan k (insert p ps) = affineSpan k ps := by
  rw [← mem_coe] at h
  rw [← affineSpan_insert_affineSpan]; rw [Set.insert_eq_of_mem h]; rw [affineSpan_coe]

variable {k}

/--
theorem `vectorSpan_insert_eq_vectorSpan` / 定理 `vectorSpan_insert_eq_vectorSpan`

English:
theorem vectorSpan_insert_eq_vectorSpan
  given: {p : P} {ps : Set P} (h : p in affineSpan k ps)
  proof: by
  simp_rw [← direction_affineSpan, affineSpan_insert_eq_affineSpan _ h]

中文:
定理 vectorSpan_insert_eq_vectorSpan
  条件: {p : P} {ps : Set P} (h : p in affineSpan k ps)
  证明: by
  simp_rw [← direction_affineSpan, affineSpan_insert_eq_affineSpan _ h]

Depends on / 依赖: affineSpan_insert_eq_affineSpan, direction_affineSpan, simp_rw
-/
theorem vectorSpan_insert_eq_vectorSpan {p : P} {ps : Set P} (h : p in affineSpan k ps) :
    vectorSpan k (insert p ps) = vectorSpan k ps := by
  simp_rw [← direction_affineSpan, affineSpan_insert_eq_affineSpan _ h]

/--
lemma `affineSpan_le_toAffineSubspace_span` / 引理 `affineSpan_le_toAffineSubspace_span`

English:
lemma affineSpan_le_toAffineSubspace_span
  given: {s : Set V}
  proof: by
  intro x hx
  simp only [Submodule.mem_toAffineSubspace]
  induction hx using affineSpan_induction' with
  | mem x hx => exact Submodule.subset_span hx
  | smul_vsub_vadd c u _ v _ w _ hu hv hw =>
    simp only [vsub_eq_sub, vadd_eq_add]
    apply Submodule.add_mem _ _ hw
    exact Submodule.smu

中文:
引理 affineSpan_le_toAffineSubspace_span
  条件: {s : Set V}
  证明: by
  intro x hx
  simp only [Submodule.mem_toAffineSubspace]
  induction hx using affineSpan_induction' with
  | mem x hx => exact Submodule.subset_span hx
  | smul_vsub_vadd c u _ v _ w _ hu hv hw =>
    simp only [vsub_eq_sub, vadd_eq_add]
    apply Submodule.add_mem _ _ hw
    exact Submodule.smu

Depends on / 依赖: Submodule, Submodule.add_mem, Submodule.mem_toAffineSubspace, Submodule.smul_mem, Submodule.sub_mem, Submodule.subset_span, add_mem, affineSpan_induction, mem_toAffineSubspace, smul_mem, smul_vsub_vadd, sub_mem, subset_span, vadd_eq_add, vsub_eq_sub
-/
lemma affineSpan_le_toAffineSubspace_span {s : Set V} :
    affineSpan k s <= (Submodule.span k s).toAffineSubspace := by
  intro x hx
  simp only [Submodule.mem_toAffineSubspace]
  induction hx using affineSpan_induction' with
  | mem x hx => exact Submodule.subset_span hx
  | smul_vsub_vadd c u _ v _ w _ hu hv hw =>
    simp only [vsub_eq_sub, vadd_eq_add]
    apply Submodule.add_mem _ _ hw
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu hv)

/--
lemma `affineSpan_subset_span` / 引理 `affineSpan_subset_span`

English:
lemma affineSpan_subset_span
  given: {s : Set V}
  proof: affineSpan_le_toAffineSubspace_span

中文:
引理 affineSpan_subset_span
  条件: {s : Set V}
  证明: affineSpan_le_toAffineSubspace_span

Depends on / 依赖: affineSpan_le_toAffineSubspace_span
-/
lemma affineSpan_subset_span {s : Set V} :
    (affineSpan k s : Set V) subseteq Submodule.span k s :=
  affineSpan_le_toAffineSubspace_span

-- TODO: We want this to be simp, but `affineSpan` gets simp-ed away to `spanPoints`!
-- Let's delete `spanPoints`
/--
lemma `affineSpan_insert_zero` / 引理 `affineSpan_insert_zero`

English:
lemma affineSpan_insert_zero
  given: (s : Set V)
  proof: by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self]; rw [vectorSpan_def]
refine Subset.trans ?_ subset_add_left _ mem_insert ..
  gcongr
exact subset_sub_left mem_insert ..

中文:
引理 affineSpan_insert_zero
  条件: (s : Set V)
  证明: by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self]; rw [vectorSpan_def]
refine Subset.trans ?_ subset_add_left _ mem_insert ..
  gcongr
exact subset_sub_left mem_insert ..

Depends on / 依赖: Submodule, Submodule.span_insert_zero, Subset, Subset.trans, affineSpan_subset_span, affineSpan_subset_span.antisymm, antisymm, mem_insert, span_insert_zero, subset_add_left, subset_sub_left, vectorSpan_add_self, vectorSpan_def
-/
lemma affineSpan_insert_zero (s : Set V) :
    (affineSpan k (insert 0 s) : Set V) = Submodule.span k s := by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self]; rw [vectorSpan_def]
refine Subset.trans ?_ subset_add_left _ mem_insert ..
  gcongr
exact subset_sub_left mem_insert ..

end AffineSpace'
