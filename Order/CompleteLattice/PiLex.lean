/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Complete linear order instance on lexicographically ordered pi types

We show that for `α` a family of complete linear orders, the lexicographically ordered type of
dependent functions `Πₗ i, α i` is itself a complete linear order.
-/

@[expose] public section

variable {ι : Type*} {α : ι -> Type*} [LinearOrder ι] [forall i, CompleteLinearOrder (α i)]

namespace Pi

/-! ### Lexicographic ordering -/

namespace Lex

/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι)
  body: ⨅ e : {e in s | forall j < i, e j = inf s j}, e.1 i
termination_by wellFounded_lt.wrap i

中文:
定义 inf
  签名: [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι)
  定义体: ⨅ e : {e in s | forall j < i, e j = inf s j}, e.1 i
termination_by wellFounded_lt.wrap i
-/
private def inf [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨅ e : {e in s | forall j < i, e j = inf s j}, e.1 i
termination_by wellFounded_lt.wrap i

variable [WellFoundedLT ι]

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Πₗ i, α i)
  body: toLex (inf s)

中文:
实例 :
  签名: InfSet (Πₗ i, α i)
  定义体: toLex (inf s)
-/
instance : InfSet (Πₗ i, α i) where
  sInf s := toLex (inf s)

/--
theorem `sInf_apply` / 定理 `sInf_apply`

English:
theorem sInf_apply
  given: (s : Set (Πₗ i, α i)) (i : ι)
  proof: by
  simp [sInf, inf]

中文:
定理 sInf_apply
  条件: (s : Set (Πₗ i, α i)) (i : ι)
  证明: by
  simp [sInf, inf]
-/
theorem sInf_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sInf s i = ⨅ e : {e in s | forall j < i, e j = sInf s j}, e.1 i := by
  simp [sInf, inf]

/--
theorem `sInf_apply_le` / 定理 `sInf_apply_le`

English:
theorem sInf_apply_le
  statement: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  proof: by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

中文:
定理 sInf_apply_le
  结论: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  证明: by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

Depends on / 依赖: sInf_apply, sInf_le
-/
theorem sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e in s) (h : forall j < i, e j = sInf s j) : sInf s i <= e i := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

/--
theorem `le_sInf_apply` / 定理 `le_sInf_apply`

English:
theorem le_sInf_apply
  statement: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  proof: by
  rw [sInf_apply]
  apply le_sInf
  grind

中文:
定理 le_sInf_apply
  结论: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  证明: by
  rw [sInf_apply]
  apply le_sInf
  grind

Depends on / 依赖: le_sInf, sInf_apply
-/
theorem le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : forall f in s, (forall j < i, f j = sInf s j) -> e i <= f i) : e i <= sInf s i := by
  rw [sInf_apply]
  apply le_sInf
  grind

/--
theorem `isGLB_sInf` / 定理 `isGLB_sInf`

English:
theorem isGLB_sInf
  given: {s : Set (Πₗ i, α i)}
  statement: IsGLB s (sInf s)
  proof: by
  refine ⟨fun e he => ?_, fun e h => ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
refine ha.2.not_ge le_sInf_apply fun f hf hf' => apply_le_of_toLex (h hf) ?_
    simp_all

中文:
定理 isGLB_sInf
  条件: {s : Set (Πₗ i, α i)}
  结论: IsGLB s (sInf s)
  证明: by
  refine ⟨fun e he => ?_, fun e h => ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
refine ha.2.not_ge le_sInf_apply fun f hf hf' => apply_le_of_toLex (h hf) ?_
    simp_all
-/
private theorem isGLB_sInf {s : Set (Πₗ i, α i)} : IsGLB s (sInf s) := by
  refine ⟨fun e he => ?_, fun e h => ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
refine ha.2.not_ge le_sInf_apply fun f hf hf' => apply_le_of_toLex (h hf) ?_
    simp_all

-- TODO: figure out how to use `to_dual` here

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (Πₗ i, α i)
  body: sInf (α := Πₗ i, (α i)ᵒᵈ) s

中文:
实例 :
  签名: SupSet (Πₗ i, α i)
  定义体: sInf (α := Πₗ i, (α i)ᵒᵈ) s
-/
instance : SupSet (Πₗ i, α i) where
  sSup s := sInf (α := Πₗ i, (α i)ᵒᵈ) s

/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: (s : Set (Πₗ i, α i)) (i : ι)
  proof: sInf_apply (α := fun i => (α i)ᵒᵈ) ..

中文:
定理 sSup_apply
  条件: (s : Set (Πₗ i, α i)) (i : ι)
  证明: sInf_apply (α := fun i => (α i)ᵒᵈ) ..

Depends on / 依赖: sInf_apply
-/
theorem sSup_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sSup s i = ⨆ e : {e in s | forall j < i, e j = sSup s j}, e.1 i :=
  sInf_apply (α := fun i => (α i)ᵒᵈ) ..

/--
theorem `le_sSup_apply` / 定理 `le_sSup_apply`

English:
theorem le_sSup_apply
  statement: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  proof: sInf_apply_le (α := fun i => (α i)ᵒᵈ) he h

中文:
定理 le_sSup_apply
  结论: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  证明: sInf_apply_le (α := fun i => (α i)ᵒᵈ) he h

Depends on / 依赖: sInf_apply_le
-/
theorem le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e in s) (h : forall j < i, e j = sSup s j) : e i <= sSup s i :=
  sInf_apply_le (α := fun i => (α i)ᵒᵈ) he h

/--
theorem `sSup_apply_le` / 定理 `sSup_apply_le`

English:
theorem sSup_apply_le
  statement: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  proof: le_sInf_apply (α := fun i => (α i)ᵒᵈ) h

中文:
定理 sSup_apply_le
  结论: {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
  证明: le_sInf_apply (α := fun i => (α i)ᵒᵈ) h

Depends on / 依赖: le_sInf_apply
-/
theorem sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : forall f in s, (forall j < i, f j = sSup s j) -> f i <= e i) : sSup s i <= e i :=
  le_sInf_apply (α := fun i => (α i)ᵒᵈ) h

/--
theorem `isLUB_sSup` / 定理 `isLUB_sSup`

English:
theorem isLUB_sSup
  given: {s : Set (Πₗ i, α i)}
  statement: IsLUB s (sSup s)
  proof: by
  refine ⟨fun e he => ?_, fun e h => ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sSup_apply he fun j hj => (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
refine ha.2.not_ge sSup_apply_le fun f hf hf' => apply_le_of_toLex (h hf) ?_
    simp_all

中文:
定理 isLUB_sSup
  条件: {s : Set (Πₗ i, α i)}
  结论: IsLUB s (sSup s)
  证明: by
  refine ⟨fun e he => ?_, fun e h => ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sSup_apply he fun j hj => (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
refine ha.2.not_ge sSup_apply_le fun f hf hf' => apply_le_of_toLex (h hf) ?_
    simp_all
-/
private theorem isLUB_sSup {s : Set (Πₗ i, α i)} : IsLUB s (sSup s) := by
  refine ⟨fun e he => ?_, fun e h => ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sSup_apply he fun j hj => (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
refine ha.2.not_ge sSup_apply_le fun f hf hf' => apply_le_of_toLex (h hf) ?_
    simp_all

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (Πₗ i, α i) where
  body: by exact isLUB_sSup
  isGLB_sInf _ := by exact isGLB_sInf

中文:
实例 completeLattice
  签名: : CompleteLattice (Πₗ i, α i) where
  定义体: by exact isLUB_sSup
  isGLB_sInf _ := by exact isGLB_sInf

Depends on / 依赖: isGLB_sInf, isLUB_sSup
-/
noncomputable instance completeLattice : CompleteLattice (Πₗ i, α i) where
  isLUB_sSup _ := by exact isLUB_sSup
  isGLB_sInf _ := by exact isGLB_sInf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLinearOrder (Πₗ i, α i)
  body: linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

中文:
实例 :
  签名: CompleteLinearOrder (Πₗ i, α i)
  定义体: linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

Depends on / 依赖: linearOrder
-/
noncomputable instance : CompleteLinearOrder (Πₗ i, α i) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Lex

/-! ### Colexicographic ordering -/

namespace Colex
variable [WellFoundedGT ι]

set_option backward.isDefEq.respectTransparency false in
@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Colex ((i : ι) -> α i))
  body: sInf (α := Πₗ i : ιᵒᵈ, α i) s

中文:
实例 :
  签名: InfSet (Colex ((i : ι) -> α i))
  定义体: sInf (α := Πₗ i : ιᵒᵈ, α i) s
-/
instance : InfSet (Colex ((i : ι) -> α i)) where
  sInf s := sInf (α := Πₗ i : ιᵒᵈ, α i) s

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sInf_apply` / 定理 `sInf_apply`

English:
theorem sInf_apply
  given: (s : Set (Colex ((i : ι) -> α i))) (i : ι)
  proof: Lex.sInf_apply (ι := ιᵒᵈ) s i

中文:
定理 sInf_apply
  条件: (s : Set (Colex ((i : ι) -> α i))) (i : ι)
  证明: Lex.sInf_apply (ι := ιᵒᵈ) s i

Depends on / 依赖: Lex.sInf_apply, sInf_apply
-/
theorem sInf_apply (s : Set (Colex ((i : ι) -> α i))) (i : ι) :
    sInf s i = ⨅ e : {e in s | forall j > i, e j = sInf s j}, e.1 i :=
  Lex.sInf_apply (ι := ιᵒᵈ) s i

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sInf_apply_le` / 定理 `sInf_apply_le`

English:
theorem sInf_apply_le
  statement: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  proof: Lex.sInf_apply_le (ι := ιᵒᵈ) he h

中文:
定理 sInf_apply_le
  结论: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  证明: Lex.sInf_apply_le (ι := ιᵒᵈ) he h

Depends on / 依赖: Lex.sInf_apply_le, sInf_apply_le
-/
theorem sInf_apply_le {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
    (he : e in s) (h : forall j > i, e j = sInf s j) : sInf s i <= e i :=
  Lex.sInf_apply_le (ι := ιᵒᵈ) he h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_sInf_apply` / 定理 `le_sInf_apply`

English:
theorem le_sInf_apply
  statement: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  proof: Lex.le_sInf_apply (ι := ιᵒᵈ) h

中文:
定理 le_sInf_apply
  结论: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  证明: Lex.le_sInf_apply (ι := ιᵒᵈ) h

Depends on / 依赖: Lex.le_sInf_apply, le_sInf_apply
-/
theorem le_sInf_apply {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
    (h : forall f in s, (forall j > i, f j = sInf s j) -> e i <= f i) : e i <= sInf s i :=
  Lex.le_sInf_apply (ι := ιᵒᵈ) h

-- TODO: figure out how to use `to_dual` here

set_option backward.isDefEq.respectTransparency false in
@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (Colex ((i : ι) -> α i))
  body: sSup (α := Πₗ i : ιᵒᵈ, α i) s

中文:
实例 :
  签名: SupSet (Colex ((i : ι) -> α i))
  定义体: sSup (α := Πₗ i : ιᵒᵈ, α i) s
-/
instance : SupSet (Colex ((i : ι) -> α i)) where
  sSup s := sSup (α := Πₗ i : ιᵒᵈ, α i) s

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: (s : Set (Colex ((i : ι) -> α i))) (i : ι)
  proof: Lex.sSup_apply (ι := ιᵒᵈ) s i

中文:
定理 sSup_apply
  条件: (s : Set (Colex ((i : ι) -> α i))) (i : ι)
  证明: Lex.sSup_apply (ι := ιᵒᵈ) s i

Depends on / 依赖: Lex.sSup_apply, sSup_apply
-/
theorem sSup_apply (s : Set (Colex ((i : ι) -> α i))) (i : ι) :
    sSup s i = ⨆ e : {e in s | forall j > i, e j = sSup s j}, e.1 i :=
  Lex.sSup_apply (ι := ιᵒᵈ) s i

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_sSup_apply` / 定理 `le_sSup_apply`

English:
theorem le_sSup_apply
  statement: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  proof: Lex.le_sSup_apply (ι := ιᵒᵈ) he h

中文:
定理 le_sSup_apply
  结论: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  证明: Lex.le_sSup_apply (ι := ιᵒᵈ) he h

Depends on / 依赖: Lex.le_sSup_apply, le_sSup_apply
-/
theorem le_sSup_apply {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
    (he : e in s) (h : forall j > i, e j = sSup s j) : e i <= sSup s i :=
  Lex.le_sSup_apply (ι := ιᵒᵈ) he h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sSup_apply_le` / 定理 `sSup_apply_le`

English:
theorem sSup_apply_le
  statement: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  proof: Lex.sSup_apply_le (ι := ιᵒᵈ) h

中文:
定理 sSup_apply_le
  结论: {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
  证明: Lex.sSup_apply_le (ι := ιᵒᵈ) h

Depends on / 依赖: Lex.sSup_apply_le, sSup_apply_le
-/
theorem sSup_apply_le {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : ι) -> α i)}
    (h : forall f in s, (forall j > i, f j = sSup s j) -> f i <= e i) : sSup s i <= e i :=
  Lex.sSup_apply_le (ι := ιᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (Colex ((i : ι) -> α i)) where
  body: by exact Lex.isLUB_sSup (ι := ιᵒᵈ)
  isGLB_sInf _ := by exact Lex.isGLB_sInf (ι := ιᵒᵈ)

中文:
实例 completeLattice
  签名: : CompleteLattice (Colex ((i : ι) -> α i)) where
  定义体: by exact Lex.isLUB_sSup (ι := ιᵒᵈ)
  isGLB_sInf _ := by exact Lex.isGLB_sInf (ι := ιᵒᵈ)

Depends on / 依赖: Lex.isGLB_sInf, Lex.isLUB_sSup, isGLB_sInf, isLUB_sSup
-/
noncomputable instance completeLattice : CompleteLattice (Colex ((i : ι) -> α i)) where
  isLUB_sSup _ := by exact Lex.isLUB_sSup (ι := ιᵒᵈ)
  isGLB_sInf _ := by exact Lex.isGLB_sInf (ι := ιᵒᵈ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLinearOrder (Colex ((i : ι) -> α i))
  body: linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

中文:
实例 :
  签名: CompleteLinearOrder (Colex ((i : ι) -> α i))
  定义体: linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

Depends on / 依赖: linearOrder
-/
noncomputable instance : CompleteLinearOrder (Colex ((i : ι) -> α i)) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Colex
end Pi
