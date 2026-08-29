/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Finitely generated monoids and groups

We define finitely generated monoids and groups. See also `Submodule.FG` and `Module.Finite` for
finitely-generated modules.

## Main definition

* `Submonoid.FG S`, `AddSubmonoid.FG S` : A submonoid `S` is finitely generated.
* `Monoid.FG M`, `AddMonoid.FG M` : A typeclass indicating a type `M` is finitely generated as a
  monoid.
* `Subgroup.FG S`, `AddSubgroup.FG S` : A subgroup `S` is finitely generated.
* `Group.FG M`, `AddGroup.FG M` : A typeclass indicating a type `M` is finitely generated as a
  group.

-/

@[expose] public section

assert_not_exists MonoidWithZero

/-! ### Monoids and submonoids -/


open scoped Pointwise

variable {M N : Type*} [Monoid M]

section Submonoid
variable [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive /-- An additive submonoid of `N` is finitely generated if it is the closure of a
finite subset of `M`. -/]
/--
Definition of `Submonoid.FG` / `Submonoid.FG` 的定义

English:
definition Submonoid.FG
  signature: (P : Submonoid M)
  body: exists S : Finset M, Submonoid.closure ↑S = P

中文:
定义 子幺半群.FG
  签名: (P : 子幺半群 M)
  定义体: exists S : Finset M, Submonoid.closure ↑S = P

Depends on / 依赖: Finset, Submonoid, Submonoid.closure, closure
-/
def Submonoid.FG (P : Submonoid M) : Prop :=
  exists S : Finset M, Submonoid.closure ↑S = P

/-- An equivalent expression of `Submonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubmonoid.FG` in terms of `Set.Finite` instead of
`Finset`. -/]
/--
theorem `Submonoid.fg_iff` / 定理 `Submonoid.fg_iff`

English:
theorem Submonoid.fg_iff
  given: (P : Submonoid M)
  proof: ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

中文:
定理 子幺半群.fg_iff
  条件: (P : 子幺半群 M)
  证明: ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

Depends on / 依赖: Finite, Finset, Finset.finite_toSet, Set.Finite.toFinset, finite_toSet, toFinset
-/
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ exists S : Set M, Submonoid.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A finitely generated submonoid has a minimal generating set. -/
@[to_additive /-- A finitely generated submonoid has a minimal generating set. -/]
/--
lemma `Submonoid.FG.exists_minimal_closure_eq` / 引理 `Submonoid.FG.exists_minimal_closure_eq`

English:
lemma Submonoid.FG.exists_minimal_closure_eq
  given: (hP : P.FG)
  proof: exists_minimal_of_wellFoundedLT _ hP

中文:
引理 子幺半群.FG.存在_minimal_closure_eq
  条件: (hP : P.FG)
  证明: exists_minimal_of_wellFoundedLT _ hP

Depends on / 依赖: exists_minimal_of_wellFoundedLT
-/
lemma Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) :
    exists S : Finset M, Minimal (fun S : Finset M => closure S = P) S :=
  exists_minimal_of_wellFoundedLT _ hP

/--
theorem `Submonoid.fg_iff_add_fg` / 定理 `Submonoid.fg_iff_add_fg`

English:
theorem Submonoid.fg_iff_add_fg
  given: (P : Submonoid M)
  statement: P.FG ↔ P.toAddSubmonoid.FG
  proof: ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Additive.ofMul ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩

中文:
定理 子幺半群.fg_iff_add_fg
  条件: (P : 子幺半群 M)
  结论: P.FG ↔ P.toAddSubmonoid.FG
  证明: ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Additive.ofMul ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩

Depends on / 依赖: AddSubmonoid, AddSubmonoid.fg_iff, AddSubmonoid.toSubmonoid, Additive, Additive.ofMul, Additive.toMul, Submonoid, Submonoid.fg_iff, Submonoid.toAddSubmonoid_closure, _closure, fg_iff, toAddSubmonoid_closure, toSubmonoid
-/
theorem Submonoid.fg_iff_add_fg (P : Submonoid M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Additive.ofMul ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩

/--
theorem `AddSubmonoid.fg_iff_mul_fg` / 定理 `AddSubmonoid.fg_iff_mul_fg`

English:
theorem AddSubmonoid.fg_iff_mul_fg
  given: {M : Type*} [AddMonoid M] (P : AddSubmonoid M)
  proof: by
  convert! (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm

@[to_additive]

中文:
定理 加法子幺半群.fg_iff_mul_fg
  条件: {M : 类型} [加法幺半群 M] (P : 加法子幺半群 M)
  证明: by
  convert! (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.fg_iff_add_fg, convert, fg_iff_add_fg, toSubmonoid
-/
theorem AddSubmonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] (P : AddSubmonoid M) :
    P.FG ↔ P.toSubmonoid.FG := by
  convert! (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm

@[to_additive]
/--
theorem `Submonoid.FG.bot` / 定理 `Submonoid.FG.bot`

English:
theorem Submonoid.FG.bot
  statement: FG (⊥ : Submonoid M)
  proof: ⟨∅, by simp⟩

@[to_additive]

中文:
定理 子幺半群.FG.bot
  结论: FG (⊥ : 子幺半群 M)
  证明: ⟨∅, by simp⟩

@[to_additive]
-/
theorem Submonoid.FG.bot : FG (⊥ : Submonoid M) :=
  ⟨∅, by simp⟩

@[to_additive]
/--
theorem `Submonoid.FG.sup` / 定理 `Submonoid.FG.sup`

English:
theorem Submonoid.FG.sup
  given: {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG)
  statement: (P ⊔ Q).FG
  proof: by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s union t, by simp [closure_union]⟩

@[to_additive]

中文:
定理 子幺半群.FG.上确界
  条件: {Q : 子幺半群 M} (hP : P.FG) (hQ : Q.FG)
  结论: (P ⊔ Q).FG
  证明: by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s union t, by simp [closure_union]⟩

@[to_additive]

Depends on / 依赖: classical, closure_union
-/
theorem Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s union t, by simp [closure_union]⟩

@[to_additive]
/--
theorem `Submonoid.FG.finset_sup` / 定理 `Submonoid.FG.finset_sup`

English:
theorem Submonoid.FG.finset_sup
  statement: {ι : Type*} (s : Finset ι) (P : ι -> Submonoid M)
  proof: Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]

中文:
定理 子幺半群.FG.finset_sup
  结论: {ι : 类型} (s : 有限集 ι) (P : ι -> 子幺半群 M)
  证明: Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]

Depends on / 依赖: Finset, Finset.sup_induction, ha.sup, sup_induction
-/
theorem Submonoid.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι -> Submonoid M)
    (hP : forall i in s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
/--
theorem `Submonoid.FG.biSup_finset` / 定理 `Submonoid.FG.biSup_finset`

English:
theorem Submonoid.FG.biSup_finset
  statement: {ι : Type*} (s : Finset ι) (P : ι -> Submonoid M)
  proof: by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]

中文:
定理 子幺半群.FG.biSup_finset
  结论: {ι : 类型} (s : 有限集 ι) (P : ι -> 子幺半群 M)
  证明: by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, finset_sup, sup_eq_iSup
-/
theorem Submonoid.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι -> Submonoid M)
    (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
/--
theorem `Submonoid.FG.biSup` / 定理 `Submonoid.FG.biSup`

English:
theorem Submonoid.FG.biSup
  statement: {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι -> Submonoid M)
  proof: by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]

中文:
定理 子幺半群.FG.biSup
  结论: {ι : 类型} {s : 集合 ι} (hs : s.有限) (P : ι -> 子幺半群 M)
  证明: by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]

Depends on / 依赖: biSup_finset, hs.toFinset, toFinset
-/
theorem Submonoid.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι -> Submonoid M)
    (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG := by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]
/--
theorem `Submonoid.FG.iSup` / 定理 `Submonoid.FG.iSup`

English:
theorem Submonoid.FG.iSup
  given: {ι : Sort*} [Finite ι] (P : ι -> Submonoid M) (hP : forall i, (P i).FG)
  proof: by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

中文:
定理 子幺半群.FG.iSup
  条件: {ι : 类型层*} [有限 ι] (P : ι -> 子幺半群 M) (hP : 对任意 i, (P i).FG)
  证明: by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

Depends on / 依赖: PLift.down, Set.finite_univ, finite_univ, i.down, iSup_plift_down
-/
theorem Submonoid.FG.iSup {ι : Sort*} [Finite ι] (P : ι -> Submonoid M) (hP : forall i, (P i).FG) :
    (iSup P).FG := by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

/-- The product of two finitely generated submonoids is finitely generated. -/
@[to_additive prod
/-- The product of two finitely generated additive submonoids is finitely generated. -/]
/--
theorem `Submonoid.FG.prod` / 定理 `Submonoid.FG.prod`

English:
theorem Submonoid.FG.prod
  given: (hP : P.FG) (hQ : Q.FG)
  statement: (P.prod Q).FG
  proof: by
  classical
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 union singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [closure_union, hbM, hbN]

中文:
定理 子幺半群.FG.乘积
  条件: (hP : P.FG) (hQ : Q.FG)
  结论: (P.乘积 Q).FG
  证明: by
  classical
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 union singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [closure_union, hbM, hbN]

Depends on / 依赖: classical, closure_union, singleton
-/
theorem Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  classical
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 union singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [closure_union, hbM, hbN]

section Pi

variable {ι : Type*} [Finite ι] {M : ι -> Type*} [forall i, Monoid (M i)] {P : forall i, Submonoid (M i)}

@[to_additive]
/--
theorem `Submonoid.iSup_map_mulSingle` / 定理 `Submonoid.iSup_map_mulSingle`

English:
theorem Submonoid.iSup_map_mulSingle
  given: [DecidableEq ι]
  proof: by
  have := Fintype.ofFinite ι
  refine iSup_map_mulSingle_le.antisymm fun x hx => ?_
  rw [← Finset.noncommProd_mulSingle x]
  exact noncommProd_mem _ _ _ _ fun i _ => mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

中文:
定理 子幺半群.iSup_map_mulSingle
  条件: [DecidableEq ι]
  证明: by
  have := Fintype.ofFinite ι
  refine iSup_map_mulSingle_le.antisymm fun x hx => ?_
  rw [← Finset.noncommProd_mulSingle x]
  exact noncommProd_mem _ _ _ _ fun i _ => mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

Depends on / 依赖: Finset, Finset.noncommProd_mulSingle, Fintype, Fintype.ofFinite, antisymm, iSup_map_mulSingle_le, iSup_map_mulSingle_le.antisymm, mem_iSup_of_mem, mem_map_of_mem, noncommProd_mem, noncommProd_mulSingle, ofFinite
-/
theorem Submonoid.iSup_map_mulSingle [DecidableEq ι] :
    ⨆ i, map (MonoidHom.mulSingle M i) (P i) = pi Set.univ P := by
  have := Fintype.ofFinite ι
  refine iSup_map_mulSingle_le.antisymm fun x hx => ?_
  rw [← Finset.noncommProd_mulSingle x]
  exact noncommProd_mem _ _ _ _ fun i _ => mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

/-- Finite product of finitely generated submonoids is finitely generated. -/
@[to_additive
/-- Finite product of finitely generated additive submonoids is finitely generated. -/]
/--
theorem `Submonoid.FG.pi` / 定理 `Submonoid.FG.pi`

English:
theorem Submonoid.FG.pi
  given: (hP : forall i, (P i).FG)
  statement: (pi Set.univ P).FG
  proof: by
  classical
  have := Fintype.ofFinite ι
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

中文:
定理 子幺半群.FG.pi
  条件: (hP : 对任意 i, (P i).FG)
  结论: (pi 集合.univ P).FG
  证明: by
  classical
  have := Fintype.ofFinite ι
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

Depends on / 依赖: Finset, Finset.coe_biUnion, Finset.coe_image, Finset.coe_univ, Finset.univ.biUnion, Fintype, Fintype.ofFinite, MonoidHom, MonoidHom.map_mclosure, MonoidHom.mulSingle, Set.biUnion_univ, biUnion, biUnion_univ, classical, closure_iUnion, coe_biUnion, coe_image, coe_univ, iSup_map_mulSingle, map_mclosure
-/
theorem Submonoid.FG.pi (hP : forall i, (P i).FG) : (pi Set.univ P).FG := by
  classical
  have := Fintype.ofFinite ι
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

end Pi

end Submonoid

section Monoid

/-- An additive monoid is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
@[mk_iff]
/--
Definition of `AddMonoid.FG` / `AddMonoid.FG` 的定义

English:
class AddMonoid.FG
  parameters: (M : Type*) [AddMonoid M]
  axioms and operations (1):
    - fg_top : (⊤ : AddSubmonoid M).FG

中文:
类 加法幺半群.FG
  参数: (M : 类型) [加法幺半群 M]
  公理与运算 (1 个):
    - fg_top : (⊤ : 加法子幺半群 M).FG
-/
class AddMonoid.FG (M : Type*) [AddMonoid M] : Prop where
  fg_top : (⊤ : AddSubmonoid M).FG

variable (M) in
/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive]
/--
Definition of `Monoid.FG` / `Monoid.FG` 的定义

English:
class Monoid.FG
  parameters: : Prop where
  axioms and operations (1):
    - fg_top : (⊤ : Submonoid M).FG

中文:
类 幺半群.FG
  参数: : 命题 where
  公理与运算 (1 个):
    - fg_top : (⊤ : 子幺半群 M).FG
-/
class Monoid.FG : Prop where
  fg_top : (⊤ : Submonoid M).FG

@[to_additive]
/--
theorem `Monoid.fg_def` / 定理 `Monoid.fg_def`

English:
theorem Monoid.fg_def
  statement: Monoid.FG M ↔ (⊤ : Submonoid M).FG
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 幺半群.fg_def
  结论: 幺半群.FG M ↔ (⊤ : 子幺半群 M).FG
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Monoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddMonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/]
/--
theorem `Monoid.fg_iff` / 定理 `Monoid.fg_iff`

English:
theorem Monoid.fg_iff
  proof: ⟨fun _ => (Submonoid.fg_iff ⊤).1 FG.fg_top, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩

中文:
定理 幺半群.fg_iff
  证明: ⟨fun _ => (Submonoid.fg_iff ⊤).1 FG.fg_top, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩

Depends on / 依赖: FG.fg_top, Submonoid, Submonoid.fg_iff, fg_iff, fg_top
-/
theorem Monoid.fg_iff :
    Monoid.FG M ↔ exists S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite :=
  ⟨fun _ => (Submonoid.fg_iff ⊤).1 FG.fg_top, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩

variable (M) in
/-- A finitely generated monoid has a minimal generating set. -/
@[to_additive /-- A finitely generated monoid has a minimal generating set. -/]
/--
lemma `Submonoid.exists_minimal_closure_eq_top` / 引理 `Submonoid.exists_minimal_closure_eq_top`

English:
lemma Submonoid.exists_minimal_closure_eq_top
  given: [Monoid.FG M]
  proof: Monoid.FG.fg_top.exists_minimal_closure_eq

中文:
引理 子幺半群.存在_minimal_closure_eq_top
  条件: [幺半群.FG M]
  证明: Monoid.FG.fg_top.exists_minimal_closure_eq

Depends on / 依赖: Monoid, Monoid.FG.fg_top.exists_minimal_closure_eq, exists_minimal_closure_eq, fg_top
-/
lemma Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] :
    exists S : Finset M, Minimal (fun S => Submonoid.closure (SetLike.coe S) = ⊤) S :=
  Monoid.FG.fg_top.exists_minimal_closure_eq

/--
theorem `Monoid.fg_iff_add_fg` / 定理 `Monoid.fg_iff_add_fg`

English:
theorem Monoid.fg_iff_add_fg
  statement: Monoid.FG M ↔ AddMonoid.FG (Additive M) where
  proof: ⟨(Submonoid.fg_iff_add_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.fg_top⟩

中文:
定理 幺半群.fg_iff_add_fg
  结论: 幺半群.FG M ↔ 加法幺半群.FG (加性 M) where
  证明: ⟨(Submonoid.fg_iff_add_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.fg_top⟩

Depends on / 依赖: FG.fg_top, Submonoid, Submonoid.fg_iff_add_fg, fg_iff_add_fg, fg_top
-/
theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) where
  mp _ := ⟨(Submonoid.fg_iff_add_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.fg_top⟩

/--
theorem `AddMonoid.fg_iff_mul_fg` / 定理 `AddMonoid.fg_iff_mul_fg`

English:
theorem AddMonoid.fg_iff_mul_fg
  given: {M : Type*} [AddMonoid M]
  proof: ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.fg_top⟩

中文:
定理 加法幺半群.fg_iff_mul_fg
  条件: {M : 类型} [加法幺半群 M]
  证明: ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.fg_top⟩

Depends on / 依赖: AddSubmonoid, AddSubmonoid.fg_iff_mul_fg, FG.fg_top, fg_iff_mul_fg, fg_top
-/
theorem AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] :
    AddMonoid.FG M ↔ Monoid.FG (Multiplicative M) where
  mp _ := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.fg_top⟩

/--
Instance `AddMonoid.fg_of_monoid_fg` / 实例 `AddMonoid.fg_of_monoid_fg`

English:
instance AddMonoid.fg_of_monoid_fg
  signature: [Monoid.FG M]
  body: Monoid.fg_iff_add_fg.1 ‹_›

中文:
实例 加法幺半群.fg_of_monoid_fg
  签名: [幺半群.FG M]
  定义体: Monoid.fg_iff_add_fg.1 ‹_›

Depends on / 依赖: Monoid, Monoid.fg_iff_add_fg, fg_iff_add_fg
-/
instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›

/--
Instance `Monoid.fg_of_addMonoid_fg` / 实例 `Monoid.fg_of_addMonoid_fg`

English:
instance Monoid.fg_of_addMonoid_fg
  signature: {M : Type*} [AddMonoid M] [AddMonoid.FG M]
  body: AddMonoid.fg_iff_mul_fg.1 ‹_›

中文:
实例 幺半群.fg_of_addMonoid_fg
  签名: {M : 类型} [加法幺半群 M] [加法幺半群.FG M]
  定义体: AddMonoid.fg_iff_mul_fg.1 ‹_›

Depends on / 依赖: AddMonoid, AddMonoid.fg_iff_mul_fg, fg_iff_mul_fg
-/
instance Monoid.fg_of_addMonoid_fg {M : Type*} [AddMonoid M] [AddMonoid.FG M] :
    Monoid.FG (Multiplicative M) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
@[to_additive]
/--
lemma `Monoid.fg_of_finite` / 引理 `Monoid.fg_of_finite`

English:
lemma Monoid.fg_of_finite
  given: [Finite M]
  statement: Monoid.FG M
  proof: by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submonoid.closure_univ⟩⟩

中文:
引理 幺半群.fg_of_finite
  条件: [有限 M]
  结论: 幺半群.FG M
  证明: by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submonoid.closure_univ⟩⟩

Depends on / 依赖: Finset, Finset.coe_univ, Finset.univ, Submonoid, Submonoid.closure_univ, closure_univ, coe_univ, nonempty_fintype
-/
lemma Monoid.fg_of_finite [Finite M] : Monoid.FG M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submonoid.closure_univ⟩⟩

end Monoid

@[to_additive]
/--
theorem `Submonoid.FG.map` / 定理 `Submonoid.FG.map`

English:
theorem Submonoid.FG.map
  given: {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M ->* M')
  proof: by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩

@[to_additive]

中文:
定理 子幺半群.FG.map
  条件: {M' : 类型} [幺半群 M'] {P : 子幺半群 M} (h : P.FG) (e : M ->* M')
  证明: by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_image, MonoidHom, MonoidHom.map_mclosure, classical, coe_image, map_mclosure, s.image
-/
theorem Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M ->* M') :
    (P.map e).FG := by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩

@[to_additive]
/--
theorem `Submonoid.FG.map_injective` / 定理 `Submonoid.FG.map_injective`

English:
theorem Submonoid.FG.map_injective
  statement: {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M ->* M')
  proof: by
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs]; rw [MonoidHom.map_mclosure e]; rw [Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff]; rw [← MonoidHom.coe_mrange e]; rw [← Submonoid.closure_le]; rw [hs]; rw [MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top

@[to_additive (attr := simp)]

中文:
定理 子幺半群.FG.map_injective
  结论: {M' : 类型} [幺半群 M'] {P : 子幺半群 M} (e : M ->* M')
  证明: by
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs]; rw [MonoidHom.map_mclosure e]; rw [Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff]; rw [← MonoidHom.coe_mrange e]; rw [← Submonoid.closure_le]; rw [hs]; rw [MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.coe_preimage, MonoidHom, MonoidHom.coe_mrange, MonoidHom.map_mclosure, MonoidHom.mrange_eq_map, Set.image_preimage_eq_iff, Submonoid, Submonoid.closure_le, Submonoid.map_injective_of_injective, Submonoid.monotone_map, closure_le, coe_mrange, coe_preimage, he.injOn, image_preimage_eq_iff, le_top, map_injective_of_injective, map_mclosure, monotone_map
-/
theorem Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M ->* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs]; rw [MonoidHom.map_mclosure e]; rw [Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff]; rw [← MonoidHom.coe_mrange e]; rw [← Submonoid.closure_le]; rw [hs]; rw [MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top

@[to_additive (attr := simp)]
/--
theorem `Monoid.fg_iff_submonoid_fg` / 定理 `Monoid.fg_iff_submonoid_fg`

English:
theorem Monoid.fg_iff_submonoid_fg
  given: (N : Submonoid M)
  statement: Monoid.FG N ↔ N.FG
  proof: by
  conv_rhs => rw [← N.mrange_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h => h.fg_top.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩

@[to_additive]

中文:
定理 幺半群.fg_iff_submonoid_fg
  条件: (N : 子幺半群 M)
  结论: 幺半群.FG N ↔ N.FG
  证明: by
  conv_rhs => rw [← N.mrange_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h => h.fg_top.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mrange_eq_map, N.mrange_subtype, N.subtype, Subtype, Subtype.coe_injective, coe_injective, conv_rhs, fg_top, h.fg_top.map, h.map_injective, map_injective, mrange_eq_map, mrange_subtype, subtype
-/
theorem Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG := by
  conv_rhs => rw [← N.mrange_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h => h.fg_top.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩

@[to_additive]
/--
theorem `Monoid.fg_of_surjective` / 定理 `Monoid.fg_of_surjective`

English:
theorem Monoid.fg_of_surjective
  statement: {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M ->* M')
  proof: by
  classical
    obtain ⟨s, hs⟩ := Monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]

@[to_additive]

中文:
定理 幺半群.fg_of_surjective
  结论: {M' : 类型} [幺半群 M'] [幺半群.FG M] (f : M ->* M')
  证明: by
  classical
    obtain ⟨s, hs⟩ := Monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_image, Monoid, Monoid.fg_def.mp, MonoidHom, MonoidHom.map_mclosure, MonoidHom.mrange_eq_map, MonoidHom.mrange_eq_top, classical, coe_image, fg_def, map_mclosure, mrange_eq_map, mrange_eq_top, s.image
-/
theorem Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M ->* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  classical
    obtain ⟨s, hs⟩ := Monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]

@[to_additive]
/--
Instance `Monoid.fg_range` / 实例 `Monoid.fg_range`

English:
instance Monoid.fg_range
  signature: {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M ->* M')
  body: Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

中文:
实例 幺半群.fg_range
  签名: {M' : 类型} [幺半群 M'] [幺半群.FG M] (f : M ->* M')
  定义体: Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

Depends on / 依赖: Monoid, Monoid.fg_of_surjective, f.mrangeRestrict, f.mrangeRestrict_surjective, fg_of_surjective, mrangeRestrict, mrangeRestrict_surjective
-/
instance Monoid.fg_range {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M ->* M') :
    Monoid.FG (MonoidHom.mrange f) :=
  Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

open FreeMonoid in
@[to_additive]
instance (α : Type*) [Finite α] : Monoid.FG (FreeMonoid α) :=
  Monoid.fg_iff.mpr ⟨Set.range of, closure_range_of, Set.finite_range of⟩

/-- A monoid is finitely generated iff there exists a surjective homomorphism from a `FreeMonoid`
on finitely many generators. -/
@[to_additive /-- An additive monoid is finitely generated iff there exists a surjective
homomorphism from a `FreeAddMonoid` on finitely many generators.-/]
/--
theorem `Monoid.fg_iff_exists_freeMonoid_hom_surjective` / 定理 `Monoid.fg_iff_exists_freeMonoid_hom_surjective`

English:
theorem Monoid.fg_iff_exists_freeMonoid_hom_surjective
  proof: by
  refine ⟨fun ⟨S, hS⟩ => ⟨S, S.finite_toSet, FreeMonoid.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.mrange_eq_top, ← Submonoid.closure_eq_mrange]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeMonoid.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_mclosure, hφ, FreeMonoid.closure_range_of, ← MonoidHom.mrange_eq_map]

中文:
定理 幺半群.fg_iff_存在_freeMonoid_hom_surjective
  证明: by
  refine ⟨fun ⟨S, hS⟩ => ⟨S, S.finite_toSet, FreeMonoid.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.mrange_eq_top, ← Submonoid.closure_eq_mrange]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeMonoid.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_mclosure, hφ, FreeMonoid.closure_range_of, ← MonoidHom.mrange_eq_map]

Depends on / 依赖: Finite, FreeMonoid, FreeMonoid.closure_range_of, FreeMonoid.lift, FreeMonoid.of, MonoidHom, MonoidHom.map_mclosure, MonoidHom.mrange_eq_map, MonoidHom.mrange_eq_top, S.finite_toSet, Set.range, Set.toFinite, Submonoid, Submonoid.closure_eq_mrange, Subtype, Subtype.val, closure_eq_mrange, closure_range_of, fg_iff, fg_iff.mpr
-/
theorem Monoid.fg_iff_exists_freeMonoid_hom_surjective :
    Monoid.FG M ↔ exists (S : Set M) (_ : S.Finite) (φ : FreeMonoid S ->* M), Function.Surjective φ := by
  refine ⟨fun ⟨S, hS⟩ => ⟨S, S.finite_toSet, FreeMonoid.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.mrange_eq_top, ← Submonoid.closure_eq_mrange]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeMonoid.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_mclosure, hφ, FreeMonoid.closure_range_of, ← MonoidHom.mrange_eq_map]

/-- A monoid if finitely generated if and only if there exists a surjective homomorphism from a
`FreeMonoid` on an arbitrary finite type `α` to the monoid. -/
@[to_additive /-- An additive monoid is finitely generated iff there exists a surjective
homomorphism from a `FreeAddMonoid` on an arbitrary finite type `α` to the monoid. -/]
/--
theorem `Monoid.fg_iff_exists_freeGroup_hom_surjective_finite` / 定理 `Monoid.fg_iff_exists_freeGroup_hom_surjective_finite`

English:
theorem Monoid.fg_iff_exists_freeGroup_hom_surjective_finite
  proof: by
  constructor
  · rw [fg_iff_exists_freeMonoid_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeMonoid.freeMonoidCongr e).symm,
      hφ.comp (FreeMonoid.freeMonoidCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Monoid.fg_of_surjective _ hφ

@[to_additive]

中文:
定理 幺半群.fg_iff_存在_freeGroup_hom_surjective_finite
  证明: by
  constructor
  · rw [fg_iff_exists_freeMonoid_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeMonoid.freeMonoidCongr e).symm,
      hφ.comp (FreeMonoid.freeMonoidCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Monoid.fg_of_surjective _ hφ

@[to_additive]

Depends on / 依赖: FreeMonoid, FreeMonoid.freeMonoidCongr, Monoid, Monoid.fg_of_surjective, exists_equiv_fin, fg_iff_exists_freeMonoid_hom_surjective, fg_of_surjective, freeMonoidCongr, hS.exists_equiv_fin, surjective, symm.surjective
-/
theorem Monoid.fg_iff_exists_freeGroup_hom_surjective_finite :
    Monoid.FG M ↔ exists (α : Type) (_ : Finite α) (φ : FreeMonoid α ->* M), Function.Surjective φ := by
  constructor
  · rw [fg_iff_exists_freeMonoid_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeMonoid.freeMonoidCongr e).symm,
      hφ.comp (FreeMonoid.freeMonoidCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Monoid.fg_of_surjective _ hφ

@[to_additive]
/--
theorem `Submonoid.powers_fg` / 定理 `Submonoid.powers_fg`

English:
theorem Submonoid.powers_fg
  given: (r : M)
  statement: (Submonoid.powers r).FG
  proof: ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

@[to_additive]

中文:
定理 子幺半群.powers_fg
  条件: (r : M)
  结论: (子幺半群.powers r).FG
  证明: ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_singleton, Submonoid, Submonoid.powers_eq_closure, coe_singleton, powers_eq_closure
-/
theorem Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG :=
  ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

@[to_additive]
/--
Instance `Monoid.powers_fg` / 实例 `Monoid.powers_fg`

English:
instance Monoid.powers_fg
  signature: (r : M)
  body: (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)

@[to_additive]

中文:
实例 幺半群.powers_fg
  签名: (r : M)
  定义体: (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)

@[to_additive]

Depends on / 依赖: Monoid, Monoid.fg_iff_submonoid_fg, Submonoid, Submonoid.powers_fg, fg_iff_submonoid_fg, powers_fg
-/
instance Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r) :=
  (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)

@[to_additive]
/--
Instance `Monoid.closure_finset_fg` / 实例 `Monoid.closure_finset_fg`

English:
instance Monoid.closure_finset_fg
  signature: (s : Finset M)
  body: by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage]; rw [Submonoid.closure_closure_coe_preimage]

@[to_additive]

中文:
实例 幺半群.closure_finset_fg
  签名: (s : 有限集 M)
  定义体: by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage]; rw [Submonoid.closure_closure_coe_preimage]

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_preimage, Submonoid, Submonoid.closure_closure_coe_preimage, Subtype, Subtype.coe_injective.injOn, Subtype.val, closure_closure_coe_preimage, coe_injective, coe_preimage, preimage, s.preimage
-/
instance Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s : Set M)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage]; rw [Submonoid.closure_closure_coe_preimage]

@[to_additive]
/--
Instance `Monoid.closure_finite_fg` / 实例 `Monoid.closure_finite_fg`

English:
instance Monoid.closure_finite_fg
  signature: (s : Set M) [Finite s]
  body: haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset

中文:
实例 幺半群.closure_finite_fg
  签名: (s : 集合 M) [有限 s]
  定义体: haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset

Depends on / 依赖: Fintype, Fintype.ofFinite, Monoid, Monoid.closure_finset_fg, closure_finset_fg, coe_toFinset, ofFinite, s.coe_toFinset, s.toFinset, toFinset
-/
instance Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset

/-! ### Groups and subgroups -/


variable {G H : Type*} [Group G] [AddGroup H]

section Subgroup

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
/--
Definition of `Subgroup.FG` / `Subgroup.FG` 的定义

English:
definition Subgroup.FG
  signature: (P : Subgroup G)
  body: exists S : Finset G, Subgroup.closure ↑S = P

中文:
定义 子群.FG
  签名: (P : 子群 G)
  定义体: exists S : Finset G, Subgroup.closure ↑S = P

Depends on / 依赖: Finset, Subgroup, Subgroup.closure, closure
-/
def Subgroup.FG (P : Subgroup G) : Prop :=
  exists S : Finset G, Subgroup.closure ↑S = P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc AddSubgroup.FG

/-- An equivalent expression of `Subgroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubgroup.fg` in terms of `Set.Finite` instead of
`Finset`. -/]
/--
theorem `Subgroup.fg_iff` / 定理 `Subgroup.fg_iff`

English:
theorem Subgroup.fg_iff
  given: (P : Subgroup G)
  proof: ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

中文:
定理 子群.fg_iff
  条件: (P : 子群 G)
  证明: ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

Depends on / 依赖: Finite, Finset, Finset.finite_toSet, Set.Finite.toFinset, finite_toSet, toFinset
-/
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ exists S : Set G, Subgroup.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive /-- An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid. -/]
/--
theorem `Subgroup.fg_iff_submonoid_fg` / 定理 `Subgroup.fg_iff_submonoid_fg`

English:
theorem Subgroup.fg_iff_submonoid_fg
  given: (P : Subgroup G)
  statement: P.FG ↔ P.toSubmonoid.FG
  proof: by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine ⟨S union S⁻¹, ?_, S.finite_toSet.union S.finite_toSet.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure

中文:
定理 子群.fg_iff_submonoid_fg
  条件: (P : 子群 G)
  结论: P.FG ↔ P.toSubmonoid.FG
  证明: by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine ⟨S union S⁻¹, ?_, S.finite_toSet.union S.finite_toSet.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure

Depends on / 依赖: S.finite_toSet.inv, S.finite_toSet.union, Subgroup, Subgroup.closure_le, Subgroup.closure_toSubmonoid, Subgroup.coe_toSubmonoid, Subgroup.subset_closure, Subgroup.toSubmonoid_le, Submonoid, Submonoid.closure_le, Submonoid.fg_iff, Submonoid.subset_closure, closure_le, closure_toSubmonoid, coe_toSubmonoid, fg_iff, finite_toSet, le_antisymm, subset_closure, toSubmonoid_le
-/
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine ⟨S union S⁻¹, ?_, S.finite_toSet.union S.finite_toSet.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure

/--
theorem `Subgroup.fg_iff_add_fg` / 定理 `Subgroup.fg_iff_add_fg`

English:
theorem Subgroup.fg_iff_add_fg
  given: (P : Subgroup G)
  statement: P.FG ↔ P.toAddSubgroup.FG
  proof: by
  rw [Subgroup.fg_iff_submonoid_fg]; rw [AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg

中文:
定理 子群.fg_iff_add_fg
  条件: (P : 子群 G)
  结论: P.FG ↔ P.toAddSubgroup.FG
  证明: by
  rw [Subgroup.fg_iff_submonoid_fg]; rw [AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg

Depends on / 依赖: AddSubgroup, AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup, Subgroup.fg_iff_submonoid_fg, Subgroup.toSubmonoid, fg_iff_addSubmonoid_fg, fg_iff_add_fg, fg_iff_submonoid_fg, toSubmonoid
-/
theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG := by
  rw [Subgroup.fg_iff_submonoid_fg]; rw [AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg

/--
theorem `AddSubgroup.fg_iff_mul_fg` / 定理 `AddSubgroup.fg_iff_mul_fg`

English:
theorem AddSubgroup.fg_iff_mul_fg
  given: (P : AddSubgroup H)
  statement: P.FG ↔ P.toSubgroup.FG
  proof: by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg]; rw [Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]

中文:
定理 加法子群.fg_iff_mul_fg
  条件: (P : 加法子群 H)
  结论: P.FG ↔ P.toSubgroup.FG
  证明: by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg]; rw [Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]

Depends on / 依赖: AddSubgroup, AddSubgroup.fg_iff_addSubmonoid_fg, AddSubgroup.toAddSubmonoid, AddSubmonoid, AddSubmonoid.fg_iff_mul_fg, Subgroup, Subgroup.fg_iff_submonoid_fg, fg_iff_addSubmonoid_fg, fg_iff_mul_fg, fg_iff_submonoid_fg, toAddSubmonoid
-/
theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG := by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg]; rw [Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]
/--
theorem `Subgroup.FG.bot` / 定理 `Subgroup.FG.bot`

English:
theorem Subgroup.FG.bot
  statement: FG (⊥ : Subgroup G)
  proof: ⟨∅, by simp⟩

@[to_additive]

中文:
定理 子群.FG.bot
  结论: FG (⊥ : 子群 G)
  证明: ⟨∅, by simp⟩

@[to_additive]
-/
theorem Subgroup.FG.bot : FG (⊥ : Subgroup G) :=
  ⟨∅, by simp⟩

@[to_additive]
/--
theorem `Subgroup.FG.sup` / 定理 `Subgroup.FG.sup`

English:
theorem Subgroup.FG.sup
  given: {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG)
  statement: (P ⊔ Q).FG
  proof: by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s union t, by simp [closure_union]⟩

@[to_additive]

中文:
定理 子群.FG.上确界
  条件: {P Q : 子群 G} (hP : P.FG) (hQ : Q.FG)
  结论: (P ⊔ Q).FG
  证明: by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s union t, by simp [closure_union]⟩

@[to_additive]

Depends on / 依赖: classical, closure_union
-/
theorem Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s union t, by simp [closure_union]⟩

@[to_additive]
/--
theorem `Subgroup.FG.finset_sup` / 定理 `Subgroup.FG.finset_sup`

English:
theorem Subgroup.FG.finset_sup
  statement: {ι : Type*} (s : Finset ι) (P : ι -> Subgroup G)
  proof: Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]

中文:
定理 子群.FG.finset_sup
  结论: {ι : 类型} (s : 有限集 ι) (P : ι -> 子群 G)
  证明: Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]

Depends on / 依赖: Finset, Finset.sup_induction, ha.sup, sup_induction
-/
theorem Subgroup.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι -> Subgroup G)
    (hP : forall i in s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
/--
theorem `Subgroup.FG.biSup_finset` / 定理 `Subgroup.FG.biSup_finset`

English:
theorem Subgroup.FG.biSup_finset
  statement: {ι : Type*} (s : Finset ι) (P : ι -> Subgroup G)
  proof: by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]

中文:
定理 子群.FG.biSup_finset
  结论: {ι : 类型} (s : 有限集 ι) (P : ι -> 子群 G)
  证明: by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, finset_sup, sup_eq_iSup
-/
theorem Subgroup.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι -> Subgroup G)
    (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
/--
theorem `Subgroup.FG.biSup` / 定理 `Subgroup.FG.biSup`

English:
theorem Subgroup.FG.biSup
  statement: {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι -> Subgroup G)
  proof: by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]

中文:
定理 子群.FG.biSup
  结论: {ι : 类型} {s : 集合 ι} (hs : s.有限) (P : ι -> 子群 G)
  证明: by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]

Depends on / 依赖: biSup_finset, hs.toFinset, toFinset
-/
theorem Subgroup.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι -> Subgroup G)
    (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG := by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]
/--
theorem `Subgroup.FG.iSup` / 定理 `Subgroup.FG.iSup`

English:
theorem Subgroup.FG.iSup
  given: {ι : Sort*} [Finite ι] (P : ι -> Subgroup G) (hP : forall i, (P i).FG)
  proof: by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

中文:
定理 子群.FG.iSup
  条件: {ι : 类型层*} [有限 ι] (P : ι -> 子群 G) (hP : 对任意 i, (P i).FG)
  证明: by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

Depends on / 依赖: PLift.down, Set.finite_univ, finite_univ, i.down, iSup_plift_down
-/
theorem Subgroup.FG.iSup {ι : Sort*} [Finite ι] (P : ι -> Subgroup G) (hP : forall i, (P i).FG) :
    (iSup P).FG := by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

/-- The product of two finitely generated subgroups is finitely generated. -/
@[to_additive prod
/-- The product of two finitely generated additive subgroups is finitely generated. -/]
/--
theorem `Subgroup.FG.prod` / 定理 `Subgroup.FG.prod`

English:
theorem Subgroup.FG.prod
  statement: {G' : Type*} [Group G'] {P : Subgroup G} {Q : Subgroup G'}
  proof: by
  rw [fg_iff_submonoid_fg] at *
  exact hP.prod hQ

中文:
定理 子群.FG.乘积
  结论: {G' : 类型} [群 G'] {P : 子群 G} {Q : 子群 G'}
  证明: by
  rw [fg_iff_submonoid_fg] at *
  exact hP.prod hQ

Depends on / 依赖: fg_iff_submonoid_fg, hP.prod
-/
theorem Subgroup.FG.prod {G' : Type*} [Group G'] {P : Subgroup G} {Q : Subgroup G'}
    (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  rw [fg_iff_submonoid_fg] at *
  exact hP.prod hQ

/-- Finite product of finitely generated subgroups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive subgroups is finitely generated. -/]
/--
theorem `Subgroup.FG.pi` / 定理 `Subgroup.FG.pi`

English:
theorem Subgroup.FG.pi
  statement: {ι : Type*} [Finite ι] {G : ι -> Type*} [forall i, Group (G i)]
  proof: by
  simp_rw [fg_iff_submonoid_fg] at *
  exact .pi hP

中文:
定理 子群.FG.pi
  结论: {ι : 类型} [有限 ι] {G : ι -> 类型} [对任意 i, 群 (G i)]
  证明: by
  simp_rw [fg_iff_submonoid_fg] at *
  exact .pi hP

Depends on / 依赖: fg_iff_submonoid_fg, simp_rw
-/
theorem Subgroup.FG.pi {ι : Type*} [Finite ι] {G : ι -> Type*} [forall i, Group (G i)]
    {P : forall i, Subgroup (G i)} (hP : forall i, (P i).FG) : (pi Set.univ P).FG := by
  simp_rw [fg_iff_submonoid_fg] at *
  exact .pi hP

end Subgroup

section Group

variable (G H)

/--
Definition of `Group.FG` / `Group.FG` 的定义

English:
class Group.FG
  parameters: : Prop where
  axioms and operations (1):
    - out : (⊤ : Subgroup G).FG

中文:
类 群.FG
  参数: : 命题 where
  公理与运算 (1 个):
    - out : (⊤ : 子群 G).FG
-/
class Group.FG : Prop where
  out : (⊤ : Subgroup G).FG

/--
Definition of `AddGroup.FG` / `AddGroup.FG` 的定义

English:
class AddGroup.FG
  parameters: : Prop where
  axioms and operations (1):
    - out : (⊤ : AddSubgroup H).FG

中文:
类 加法群.FG
  参数: : 命题 where
  公理与运算 (1 个):
    - out : (⊤ : 加法子群 H).FG
-/
class AddGroup.FG : Prop where
  out : (⊤ : AddSubgroup H).FG

attribute [to_additive] Group.FG

variable {G H}

/--
theorem `Group.fg_def` / 定理 `Group.fg_def`

English:
theorem Group.fg_def
  statement: Group.FG G ↔ (⊤ : Subgroup G).FG
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 群.fg_def
  结论: 群.FG G ↔ (⊤ : 子群 G).FG
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `AddGroup.fg_def` / 定理 `AddGroup.fg_def`

English:
theorem AddGroup.fg_def
  statement: AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 加法群.fg_def
  结论: 加法群.FG H ↔ (⊤ : 加法子群 H).FG
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Group.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddGroup.fg` in terms of `Set.Finite` instead of `Finset`. -/]
/--
theorem `Group.fg_iff` / 定理 `Group.fg_iff`

English:
theorem Group.fg_iff
  statement: Group.FG G ↔ exists S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite
  proof: ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩

@[to_additive]

中文:
定理 群.fg_iff
  结论: 群.FG G ↔ 存在 S : 集合 G, 子群.closure S = (⊤ : 子群 G) ∧ S.有限
  证明: ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.fg_iff, fg_iff, h.out
-/
theorem Group.fg_iff : Group.FG G ↔ exists S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite :=
  ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩

@[to_additive]
/--
theorem `Group.fg_iff'` / 定理 `Group.fg_iff'`

English:
theorem Group.fg_iff'
  proof: Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

中文:
定理 群.fg_iff'
  证明: Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

Depends on / 依赖: Group.fg_def.trans, S.card, fg_def
-/
theorem Group.fg_iff' :
    Group.FG G ↔ exists (n : _) (S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive /-- An additive group is finitely generated if and only
if it is finitely generated as an additive monoid. -/]
/--
theorem `Group.fg_iff_monoid_fg` / 定理 `Group.fg_iff_monoid_fg`

English:
theorem Group.fg_iff_monoid_fg
  statement: Group.FG G ↔ Monoid.FG G
  proof: ⟨fun h => Monoid.fg_def.2 (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
Group.fg_def.2 (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩

@[to_additive]

中文:
定理 群.fg_iff_monoid_fg
  结论: 群.FG G ↔ 幺半群.FG G
  证明: ⟨fun h => Monoid.fg_def.2 (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
Group.fg_def.2 (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩

@[to_additive]

Depends on / 依赖: Group.fg_def, Monoid, Monoid.fg_def, Subgroup, Subgroup.fg_iff_submonoid_fg, fg_def, fg_iff_submonoid_fg
-/
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G :=
⟨fun h => Monoid.fg_def.2 (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
Group.fg_def.2 (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩

@[to_additive]
/--
Instance `Monoid.fg_of_group_fg` / 实例 `Monoid.fg_of_group_fg`

English:
instance Monoid.fg_of_group_fg
  signature: [Group.FG G]
  body: Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]

中文:
实例 幺半群.fg_of_group_fg
  签名: [群.FG G]
  定义体: Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]

Depends on / 依赖: Group.fg_iff_monoid_fg, fg_iff_monoid_fg
-/
instance Monoid.fg_of_group_fg [Group.FG G] : Monoid.FG G :=
  Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]
/--
theorem `Group.fg_iff_subgroup_fg` / 定理 `Group.fg_iff_subgroup_fg`

English:
theorem Group.fg_iff_subgroup_fg
  given: (H : Subgroup G)
  statement: Group.FG H ↔ H.FG
  proof: (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm

中文:
定理 群.fg_iff_subgroup_fg
  条件: (H : 子群 G)
  结论: 群.FG H ↔ H.FG
  证明: (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm

Depends on / 依赖: Monoid, Monoid.fg_iff_submonoid_fg, Subgroup, Subgroup.fg_iff_submonoid_fg, fg_iff_monoid_fg, fg_iff_monoid_fg.trans, fg_iff_submonoid_fg
-/
theorem Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG :=
  (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm

/--
theorem `GroupFG.iff_add_fg` / 定理 `GroupFG.iff_add_fg`

English:
theorem GroupFG.iff_add_fg
  statement: Group.FG G ↔ AddGroup.FG (Additive G)
  proof: ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩

中文:
定理 GroupFG.iff_add_fg
  结论: 群.FG G ↔ 加法群.FG (加性 G)
  证明: ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩

Depends on / 依赖: Subgroup, Subgroup.fg_iff_add_fg, fg_iff_add_fg, h.out
-/
theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) :=
  ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩

/--
theorem `AddGroup.fg_iff_mul_fg` / 定理 `AddGroup.fg_iff_mul_fg`

English:
theorem AddGroup.fg_iff_mul_fg
  statement: AddGroup.FG H ↔ Group.FG (Multiplicative H)
  proof: ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩

中文:
定理 加法群.fg_iff_mul_fg
  结论: 加法群.FG H ↔ 群.FG (Multiplicative H)
  证明: ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.fg_iff_mul_fg, fg_iff_mul_fg, h.out
-/
theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) :=
  ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩

/--
Instance `AddGroup.fg_of_group_fg` / 实例 `AddGroup.fg_of_group_fg`

English:
instance AddGroup.fg_of_group_fg
  signature: [Group.FG G]
  body: GroupFG.iff_add_fg.1 ‹_›

中文:
实例 加法群.fg_of_group_fg
  签名: [群.FG G]
  定义体: GroupFG.iff_add_fg.1 ‹_›

Depends on / 依赖: GroupFG, GroupFG.iff_add_fg, iff_add_fg
-/
instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›

/--
Instance `Group.fg_of_mul_group_fg` / 实例 `Group.fg_of_mul_group_fg`

English:
instance Group.fg_of_mul_group_fg
  signature: [AddGroup.FG H]
  body: AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]

中文:
实例 群.fg_of_mul_group_fg
  签名: [加法群.FG H]
  定义体: AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]

Depends on / 依赖: AddGroup, AddGroup.fg_iff_mul_fg, fg_iff_mul_fg
-/
instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G := by
  cases nonempty_fintype G
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Subgroup.closure_univ⟩⟩

@[to_additive]
/--
theorem `Group.fg_of_surjective` / 定理 `Group.fg_of_surjective`

English:
theorem Group.fg_of_surjective
  statement: {G' : Type*} [Group G'] [hG : Group.FG G] {f : G ->* G'}
  proof: Group.fg_iff_monoid_fg.mpr
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf

中文:
定理 群.fg_of_surjective
  结论: {G' : 类型} [群 G'] [hG : 群.FG G] {f : G ->* G'}
  证明: Group.fg_iff_monoid_fg.mpr
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf

Depends on / 依赖: Group.fg_iff_monoid_fg.mp, Group.fg_iff_monoid_fg.mpr, Monoid, Monoid.fg_of_surjective, fg_iff_monoid_fg, fg_of_surjective
-/
theorem Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G ->* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
Group.fg_iff_monoid_fg.mpr
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf

open FreeGroup in
@[to_additive]
instance (α : Type*) [Finite α] : Group.FG (FreeGroup α) :=
  Group.fg_iff.mpr ⟨Set.range of, closure_range_of α, Set.finite_range of⟩

/-- A group is finitely generated iff there exists a surjective homomorphism from a `FreeGroup`
on finitely many generators. -/
@[to_additive /-- An additive group is finitely generated iff there exists a surjective homomorphism
from a `FreeAddGroup` on finitely many generators. -/]
/--
theorem `Group.fg_iff_exists_freeGroup_hom_surjective` / 定理 `Group.fg_iff_exists_freeGroup_hom_surjective`

English:
theorem Group.fg_iff_exists_freeGroup_hom_surjective
  proof: by
  refine ⟨fun ⟨S, hS⟩ => ⟨S, S.finite_toSet, FreeGroup.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact Group.fg_of_surjective hφ

中文:
定理 群.fg_iff_存在_freeGroup_hom_surjective
  证明: by
  refine ⟨fun ⟨S, hS⟩ => ⟨S, S.finite_toSet, FreeGroup.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact Group.fg_of_surjective hφ

Depends on / 依赖: Finite, FreeGroup, FreeGroup.closure_eq_range, FreeGroup.lift, Group.fg_of_surjective, MonoidHom, MonoidHom.range_eq_top, S.finite_toSet, Subtype, Subtype.val, closure_eq_range, fg_of_surjective, finite_toSet, range_eq_top
-/
theorem Group.fg_iff_exists_freeGroup_hom_surjective :
    Group.FG G ↔ exists (S : Set G) (_ : S.Finite) (φ : FreeGroup S ->* G), Function.Surjective φ := by
  refine ⟨fun ⟨S, hS⟩ => ⟨S, S.finite_toSet, FreeGroup.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact Group.fg_of_surjective hφ

/-- A group if finitely generated if and only if there exists a surjective homomorphism from a
`FreeGroup` on an arbitrary finite type `α` to the group. -/
@[to_additive /-- An additive group is finitely generated iff there exists a surjective homomorphism
from a `FreeAddGroup` on an arbitrary finite type `α` to the group. -/]
/--
theorem `Group.fg_iff_exists_freeGroup_hom_surjective_finite` / 定理 `Group.fg_iff_exists_freeGroup_hom_surjective_finite`

English:
theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite
  proof: by
  constructor
  · rw [fg_iff_exists_freeGroup_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeGroup.freeGroupCongr e).symm,
      hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Group.fg_of_surjective hφ

@[to_additive]

中文:
定理 群.fg_iff_存在_freeGroup_hom_surjective_finite
  证明: by
  constructor
  · rw [fg_iff_exists_freeGroup_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeGroup.freeGroupCongr e).symm,
      hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Group.fg_of_surjective hφ

@[to_additive]

Depends on / 依赖: FreeGroup, FreeGroup.freeGroupCongr, Group.fg_of_surjective, exists_equiv_fin, fg_iff_exists_freeGroup_hom_surjective, fg_of_surjective, freeGroupCongr, hS.exists_equiv_fin, surjective, symm.surjective
-/
theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite :
    Group.FG G ↔ exists (α : Type) (_ : Finite α) (φ : FreeGroup α ->* G), Function.Surjective φ := by
  constructor
  · rw [fg_iff_exists_freeGroup_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeGroup.freeGroupCongr e).symm,
      hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Group.fg_of_surjective hφ

@[to_additive]
/--
Instance `Group.fg_range` / 实例 `Group.fg_range`

English:
instance Group.fg_range
  signature: {G' : Type*} [Group G'] [Group.FG G] (f : G ->* G')
  body: Group.fg_of_surjective f.rangeRestrict_surjective

@[to_additive]

中文:
实例 群.fg_range
  签名: {G' : 类型} [群 G'] [群.FG G] (f : G ->* G')
  定义体: Group.fg_of_surjective f.rangeRestrict_surjective

@[to_additive]

Depends on / 依赖: Group.fg_of_surjective, f.rangeRestrict_surjective, fg_of_surjective, rangeRestrict_surjective
-/
instance Group.fg_range {G' : Type*} [Group G'] [Group.FG G] (f : G ->* G') : Group.FG f.range :=
  Group.fg_of_surjective f.rangeRestrict_surjective

@[to_additive]
/--
Instance `Group.closure_finset_fg` / 实例 `Group.closure_finset_fg`

English:
instance Group.closure_finset_fg
  signature: (s : Finset G)
  body: by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage]; rw [← Subgroup.coe_subtype]; rw [Subgroup.closure_preimage_eq_top]

@[to_additive]

中文:
实例 群.closure_finset_fg
  签名: (s : 有限集 G)
  定义体: by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage]; rw [← Subgroup.coe_subtype]; rw [Subgroup.closure_preimage_eq_top]

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_preimage, Subgroup, Subgroup.closure_preimage_eq_top, Subgroup.coe_subtype, Subtype, Subtype.coe_injective.injOn, Subtype.val, closure_preimage_eq_top, coe_injective, coe_preimage, coe_subtype, preimage, s.preimage
-/
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage]; rw [← Subgroup.coe_subtype]; rw [Subgroup.closure_preimage_eq_top]

@[to_additive]
/--
Instance `Group.closure_finite_fg` / 实例 `Group.closure_finite_fg`

English:
instance Group.closure_finite_fg
  signature: (s : Set G) [Finite s]
  body: haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset

中文:
实例 群.closure_finite_fg
  签名: (s : 集合 G) [有限 s]
  定义体: haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset

Depends on / 依赖: Fintype, Fintype.ofFinite, Group.closure_finset_fg, closure_finset_fg, coe_toFinset, ofFinite, s.coe_toFinset, s.toFinset, toFinset
-/
instance Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset

end Group

section QuotientGroup

@[to_additive]
/--
Instance `QuotientGroup.fg` / 实例 `QuotientGroup.fg`

English:
instance QuotientGroup.fg
  signature: [Group.FG G] (N : Subgroup G) [Subgroup.Normal N]
  body: Group.fg_of_surjective QuotientGroup.mk'_surjective N

中文:
实例 商群.fg
  签名: [群.FG G] (N : 子群 G) [子群.正规 N]
  定义体: Group.fg_of_surjective QuotientGroup.mk'_surjective N

Depends on / 依赖: Group.fg_of_surjective, QuotientGroup, QuotientGroup.mk, _surjective, fg_of_surjective
-/
instance QuotientGroup.fg [Group.FG G] (N : Subgroup G) [Subgroup.Normal N] : Group.FG G ⧸ N :=
Group.fg_of_surjective QuotientGroup.mk'_surjective N

end QuotientGroup

namespace Prod

variable [Monoid N] {G' : Type*} [Group G']

open Monoid in
/-- The product of two finitely generated monoids is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive monoids is finitely generated. -/]
/--
Instance `instMonoidFG` / 实例 `instMonoidFG`

English:
instance instMonoidFG
  signature: [FG M] [FG N]
  body: by
    rw [← Submonoid.top_prod_top]
    exact ‹FG M›.fg_top.prod ‹FG N›.fg_top

中文:
实例 instMonoidFG
  签名: [FG M] [FG N]
  定义体: by
    rw [← Submonoid.top_prod_top]
    exact ‹FG M›.fg_top.prod ‹FG N›.fg_top

Depends on / 依赖: Submonoid, Submonoid.top_prod_top, fg_top, fg_top.prod, top_prod_top
-/
instance instMonoidFG [FG M] [FG N] : FG (M × N) where
  fg_top := by
    rw [← Submonoid.top_prod_top]
    exact ‹FG M›.fg_top.prod ‹FG N›.fg_top

open Group in
/-- The product of two finitely generated groups is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive groups is finitely generated. -/]
/--
Instance `instGroupFG` / 实例 `instGroupFG`

English:
instance instGroupFG
  signature: [FG G] [FG G']
  body: by
    rw [← Subgroup.top_prod_top]
    exact ‹FG G›.out.prod ‹FG G'›.out

中文:
实例 instGroupFG
  签名: [FG G] [FG G']
  定义体: by
    rw [← Subgroup.top_prod_top]
    exact ‹FG G›.out.prod ‹FG G'›.out

Depends on / 依赖: Subgroup, Subgroup.top_prod_top, out.prod, top_prod_top
-/
instance instGroupFG [FG G] [FG G'] : FG (G × G') where
  out := by
    rw [← Subgroup.top_prod_top]
    exact ‹FG G›.out.prod ‹FG G'›.out

end Prod

namespace Pi

variable {ι : Type*} [Finite ι]

/-- Finite product of finitely generated monoids is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive monoids is finitely generated. -/]
/--
Instance `instMonoidFG` / 实例 `instMonoidFG`

English:
instance instMonoidFG
  signature: {M : ι -> Type*} [forall i, Monoid (M i)] [forall i, Monoid.FG (M i)]
  body: by
    rw [← Submonoid.pi_top Set.univ]
    exact .pi fun i => Monoid.FG.fg_top

中文:
实例 instMonoidFG
  签名: {M : ι -> 类型} [对任意 i, 幺半群 (M i)] [对任意 i, 幺半群.FG (M i)]
  定义体: by
    rw [← Submonoid.pi_top Set.univ]
    exact .pi fun i => Monoid.FG.fg_top

Depends on / 依赖: Monoid, Monoid.FG.fg_top, Set.univ, Submonoid, Submonoid.pi_top, fg_top, pi_top
-/
instance instMonoidFG {M : ι -> Type*} [forall i, Monoid (M i)] [forall i, Monoid.FG (M i)] :
    Monoid.FG (forall i, M i) where
  fg_top := by
    rw [← Submonoid.pi_top Set.univ]
    exact .pi fun i => Monoid.FG.fg_top

/-- Finite product of finitely generated groups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive groups is finitely generated. -/]
/--
Instance `instGroupFG` / 实例 `instGroupFG`

English:
instance instGroupFG
  signature: {G : ι -> Type*} [forall i, Group (G i)] [forall i, Group.FG (G i)]
  body: by
    rw [← Subgroup.pi_top Set.univ]
    exact .pi fun i => Group.FG.out

中文:
实例 instGroupFG
  签名: {G : ι -> 类型} [对任意 i, 群 (G i)] [对任意 i, 群.FG (G i)]
  定义体: by
    rw [← Subgroup.pi_top Set.univ]
    exact .pi fun i => Group.FG.out

Depends on / 依赖: Group.FG.out, Set.univ, Subgroup, Subgroup.pi_top, pi_top
-/
instance instGroupFG {G : ι -> Type*} [forall i, Group (G i)] [forall i, Group.FG (G i)] :
    Group.FG (forall i, G i) where
  out := by
    rw [← Subgroup.pi_top Set.univ]
    exact .pi fun i => Group.FG.out

end Pi

namespace AddMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FG Nat
  body: ⟨{1}, by simp⟩

中文:
实例 :
  签名: FG 自然数
  定义体: ⟨{1}, by simp⟩
-/
instance : FG Nat where
  fg_top := ⟨{1}, by simp⟩

end AddMonoid

namespace AddGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FG Int
  body: ⟨{1}, by simp⟩

中文:
实例 :
  签名: FG 整数
  定义体: ⟨{1}, by simp⟩
-/
instance : FG Int where
  out := ⟨{1}, by simp⟩

end AddGroup

section WellQuasiOrderedLE

variable {M N : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M]
  [IsOrderedCancelMonoid M] [CanonicallyOrderedMul M]

/-- In a canonically ordered and well-quasi-ordered monoid, any divisive submonoid is finitely
generated. -/
@[to_additive fg_of_subtractive /-- In a canonically ordered and well-quasi-ordered additive monoid
(typical example is `ℕ ^ k`), any subtractive submonoid is finitely generated. -/]
/--
theorem `Submonoid.fg_of_divisive` / 定理 `Submonoid.fg_of_divisive`

English:
theorem Submonoid.fg_of_divisive
  given: {P : Submonoid M} (hP : forall x in P, forall y, x * y in P -> y in P)
  proof: by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x in P ∧ x != 1 }
  rw [fg_iff]
  refine ⟨_, ?_, (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOfPred_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOfPred_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 1
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [Set.mem_ofPred_eq, and_imp] at ih
    by_cases hy₃ : Minimal (· in { x | x in P ∧ x != 1 }) y
    · exact mem_closure_of_mem hy₃
    rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
    rcases exists_mul_of_le hz₁.le with ⟨y, rfl⟩
    apply mul_mem
    · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge
    apply ih
    · exact hP _ hz₂ _ hy₁
    · exact (one_lt_of_lt_mul_right hz₁).ne.symm
    · exact le_mul_self
    · rw [mul_le_iff_le_one_left']
      exact (one_lt_of_ne_one hz₃).not_ge

中文:
定理 子幺半群.fg_of_divisive
  条件: {P : 子幺半群 M} (hP : 对任意 x in P, 对任意 y, x * y in P -> y in P)
  证明: by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x in P ∧ x != 1 }
  rw [fg_iff]
  refine ⟨_, ?_, (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOfPred_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOfPred_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 1
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [Set.mem_ofPred_eq, and_imp] at ih
    by_cases hy₃ : Minimal (· in { x | x in P ∧ x != 1 }) y
    · exact mem_closure_of_mem hy₃
    rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
    rcases exists_mul_of_le hz₁.le with ⟨y, rfl⟩
    apply mul_mem
    · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge
    apply ih
    · exact hP _ hz₂ _ hy₁
    · exact (one_lt_of_lt_mul_right hz₁).ne.symm
    · exact le_mul_self
    · rw [mul_le_iff_le_one_left']
      exact (one_lt_of_ne_one hz₃).not_ge

Depends on / 依赖: And.left, P.closure_eq, Set.isPWO_of_wellQuasiOrderedLE, Set.mem_ofPred_eq, and_imp, by_c, closure_eq, closure_mono, fg_iff, finite_of_partiallyWellOrderedOn, hpwo.mono, hpwo.wellFoundedOn.induction, isPWO_of_wellQuasiOrderedLE, mem_ofPred_eq, setOfPred_minimal_antichain, setOfPred_minimal_subset, wellFoundedOn
-/
theorem Submonoid.fg_of_divisive {P : Submonoid M} (hP : forall x in P, forall y, x * y in P -> y in P) :
    P.FG := by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x in P ∧ x != 1 }
  rw [fg_iff]
  refine ⟨_, ?_, (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOfPred_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOfPred_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 1
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [Set.mem_ofPred_eq, and_imp] at ih
    by_cases hy₃ : Minimal (· in { x | x in P ∧ x != 1 }) y
    · exact mem_closure_of_mem hy₃
    rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
    rcases exists_mul_of_le hz₁.le with ⟨y, rfl⟩
    apply mul_mem
    · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge
    apply ih
    · exact hP _ hz₂ _ hy₁
    · exact (one_lt_of_lt_mul_right hz₁).ne.symm
    · exact le_mul_self
    · rw [mul_le_iff_le_one_left']
      exact (one_lt_of_ne_one hz₃).not_ge

/-- A canonically ordered and well-quasi-ordered monoid must be finitely generated. -/
@[to_additive /-- A canonically ordered and well-quasi-ordered additive monoid must be finitely
generated. -/]
/--
theorem `CommMonoid.fg_of_wellQuasiOrderedLE` / 定理 `CommMonoid.fg_of_wellQuasiOrderedLE`

English:
theorem CommMonoid.fg_of_wellQuasiOrderedLE
  statement: Monoid.FG M where
  proof: Submonoid.fg_of_divisive (by simp)

中文:
定理 交换幺半群.fg_of_wellQuasiOrderedLE
  结论: 幺半群.FG M where
  证明: Submonoid.fg_of_divisive (by simp)

Depends on / 依赖: Submonoid, Submonoid.fg_of_divisive, fg_of_divisive
-/
theorem CommMonoid.fg_of_wellQuasiOrderedLE : Monoid.FG M where
  fg_top := Submonoid.fg_of_divisive (by simp)

/-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered monoid `M` to a
cancellative monoid `N`, the submonoid of `M` on which `f` and `g` agree is finitely generated. -/
@[to_additive /-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered
additive monoid `M` to a cancellative additive monoid `N`, the submonoid of `M` on which `f` and `g`
agree is finitely generated. When `M` and `N` are `ℕ ^ k`, this is also known as a version of
**Gordan's lemma**. -/]
/--
theorem `Submonoid.fg_eqLocusM` / 定理 `Submonoid.fg_eqLocusM`

English:
theorem Submonoid.fg_eqLocusM
  given: [Monoid N] [IsCancelMul N] (f g : M ->* N)
  statement: (f.eqLocusM g).FG
  proof: fg_of_divisive (by simp_all)

中文:
定理 子幺半群.fg_eqLocusM
  条件: [幺半群 N] [是消去乘法 N] (f g : M ->* N)
  结论: (f.eqLocusM g).FG
  证明: fg_of_divisive (by simp_all)

Depends on / 依赖: fg_of_divisive
-/
theorem Submonoid.fg_eqLocusM [Monoid N] [IsCancelMul N] (f g : M ->* N) : (f.eqLocusM g).FG :=
  fg_of_divisive (by simp_all)

end WellQuasiOrderedLE
