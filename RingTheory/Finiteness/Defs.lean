/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Algebraize

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Submodule.FG`, `Ideal.FG`
  These express that some object is finitely generated as *submodule* over some base ring.

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.

-/

@[expose] public section

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/--
Definition of `FG` / `FG` 的定义

English:
definition FG
  signature: (N : Submodule R M)
  body: exists S : Finset M, span R ↑S = N

中文:
定义 FG
  签名: (N : 子模 R M)
  定义体: exists S : Finset M, span R ↑S = N

Depends on / 依赖: Finset
-/
def FG (N : Submodule R M) : Prop :=
  exists S : Finset M, span R ↑S = N

/--
theorem `fg_def` / 定理 `fg_def`

English:
theorem fg_def
  given: {N : Submodule R M}
  statement: N.FG ↔ exists S : Set M, S.Finite ∧ span R S = N
  proof: by
  refine ⟨fun ⟨t, h⟩ => ⟨_, t.finite_toSet, h⟩, ?_⟩
  rintro ⟨t', h, rfl⟩
  have := h.exists_finset_coe
  tauto

中文:
定理 fg_def
  条件: {N : 子模 R M}
  结论: N.FG ↔ 存在 S : 集合 M, S.有限 ∧ span R S = N
  证明: by
  refine ⟨fun ⟨t, h⟩ => ⟨_, t.finite_toSet, h⟩, ?_⟩
  rintro ⟨t', h, rfl⟩
  have := h.exists_finset_coe
  tauto

Depends on / 依赖: exists_finset_coe, finite_toSet, h.exists_finset_coe, t.finite_toSet
-/
theorem fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, S.Finite ∧ span R S = N := by
  refine ⟨fun ⟨t, h⟩ => ⟨_, t.finite_toSet, h⟩, ?_⟩
  rintro ⟨t', h, rfl⟩
  have := h.exists_finset_coe
  tauto

/--
theorem `fg_iff_addSubmonoid_fg` / 定理 `fg_iff_addSubmonoid_fg`

English:
theorem fg_iff_addSubmonoid_fg
  given: (P : Submodule Nat M)
  statement: P.FG ↔ P.toAddSubmonoid.FG
  proof: ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure] using hS⟩⟩

中文:
定理 fg_iff_addSubmonoid_fg
  条件: (P : 子模 自然数 M)
  结论: P.FG ↔ P.toAddSubmonoid.FG
  证明: ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure] using hS⟩⟩

Depends on / 依赖: span_nat_eq_addSubmonoidClosure
-/
theorem fg_iff_addSubmonoid_fg (P : Submodule Nat M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure] using hS⟩⟩

/--
theorem `fg_iff_addSubgroup_fg` / 定理 `fg_iff_addSubgroup_fg`

English:
theorem fg_iff_addSubgroup_fg
  given: {G : Type*} [AddCommGroup G] (P : Submodule Int G)
  proof: ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure] using hS⟩⟩

中文:
定理 fg_iff_addSubgroup_fg
  条件: {G : 类型} [加法交换群 G] (P : 子模 整数 G)
  证明: ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure] using hS⟩⟩

Depends on / 依赖: span_int_eq_addSubgroupClosure
-/
theorem fg_iff_addSubgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule Int G) :
    P.FG ↔ P.toAddSubgroup.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure] using hS⟩⟩

/--
theorem `fg_iff_exists_fin_generating_family` / 定理 `fg_iff_exists_fin_generating_family`

English:
theorem fg_iff_exists_fin_generating_family
  given: {N : Submodule R M}
  proof: by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

universe w v u in

中文:
定理 fg_iff_存在_fin_generating_family
  条件: {N : 子模 R M}
  证明: by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

universe w v u in

Depends on / 依赖: Sfin.fin_embedding, fg_def, fin_embedding, finite_range
-/
theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.FG ↔ exists (n : Nat) (s : Fin n -> M), span R (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

universe w v u in
/--
lemma `fg_iff_exists_finite_generating_family` / 引理 `fg_iff_exists_finite_generating_family`

English:
lemma fg_iff_exists_finite_generating_family
  statement: {A : Type u} [Semiring A] {M : Type v}
  proof: by
  constructor
  · intro hN
    obtain ⟨n, f, h⟩ := fg_iff_exists_fin_generating_family.mp hN
    refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
    convert! h
    ext
    simp
  · rintro ⟨G, _, g, hg⟩
    have := Fintype.ofFinite (range g)
    exact ⟨(range g).toFinset, by simpa⟩

中文:
引理 fg_iff_存在_finite_generating_family
  结论: {A : 类型u} [半环 A] {M : 类型v}
  证明: by
  constructor
  · intro hN
    obtain ⟨n, f, h⟩ := fg_iff_exists_fin_generating_family.mp hN
    refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
    convert! h
    ext
    simp
  · rintro ⟨G, _, g, hg⟩
    have := Fintype.ofFinite (range g)
    exact ⟨(range g).toFinset, by simpa⟩

Depends on / 依赖: Fintype, Fintype.ofFinite, ULift.down, convert, fg_iff_exists_fin_generating_family, fg_iff_exists_fin_generating_family.mp, ofFinite, toFinset
-/
lemma fg_iff_exists_finite_generating_family {A : Type u} [Semiring A] {M : Type v}
    [AddCommMonoid M] [Module A M] {N : Submodule A M} :
    N.FG ↔ exists (G : Type w) (_ : Finite G) (g : G -> M), span A (range g) = N := by
  constructor
  · intro hN
    obtain ⟨n, f, h⟩ := fg_iff_exists_fin_generating_family.mp hN
    refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
    convert! h
    ext
    simp
  · rintro ⟨G, _, g, hg⟩
    have := Fintype.ofFinite (range g)
    exact ⟨(range g).toFinset, by simpa⟩

/--
theorem `fg_span_iff_fg_span_finset_subset` / 定理 `fg_span_iff_fg_span_finset_subset`

English:
theorem fg_span_iff_fg_span_finset_subset
  given: (s : Set M)
  proof: by
  constructor
  · intro ⟨s'', hs''⟩
obtain ⟨s', hs's, hss'⟩ := subset_span_finite_of_subset_span hs'' ▸ subset_span
    refine ⟨s', hs's, ?_⟩
    apply le_antisymm
    · rwa [← hs'', span_le]
    · rw [span_le]
      exact le_trans hs's subset_span
  · intro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

中文:
定理 fg_span_iff_fg_span_finset_subset
  条件: (s : 集合 M)
  证明: by
  constructor
  · intro ⟨s'', hs''⟩
obtain ⟨s', hs's, hss'⟩ := subset_span_finite_of_subset_span hs'' ▸ subset_span
    refine ⟨s', hs's, ?_⟩
    apply le_antisymm
    · rwa [← hs'', span_le]
    · rw [span_le]
      exact le_trans hs's subset_span
  · intro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

Depends on / 依赖: h.symm, le_antisymm, le_trans, span_le, subset_span, subset_span_finite_of_subset_span
-/
theorem fg_span_iff_fg_span_finset_subset (s : Set M) :
    (span R s).FG ↔ exists s' : Finset M, ↑s' subseteq s ∧ span R s = span R s' := by
  constructor
  · intro ⟨s'', hs''⟩
obtain ⟨s', hs's, hss'⟩ := subset_span_finite_of_subset_span hs'' ▸ subset_span
    refine ⟨s', hs's, ?_⟩
    apply le_antisymm
    · rwa [← hs'', span_le]
    · rw [span_le]
      exact le_trans hs's subset_span
  · intro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

end Submodule

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `FG` / `FG` 的定义

English:
definition FG
  signature: (I : Ideal R)
  body: exists S : Finset R, span ↑S = I

中文:
定义 FG
  签名: (I : 理想 R)
  定义体: exists S : Finset R, span ↑S = I

Depends on / 依赖: Finset
-/
def FG (I : Ideal R) : Prop :=
  exists S : Finset R, span ↑S = I

end Ideal

section ModuleAndAlgebra

variable (R A B M N : Type*)

/--
Definition of `Module.Finite` / `Module.Finite` 的定义

English:
class Module.Finite
  parameters: [Semiring R] [AddCommMonoid M] [Module R M]
  axioms and operations (1):
    - of_fg_top : : fg_top : (⊤ : Submodule R M).FG

中文:
类 模.有限
  参数: [半环 R] [加法交换幺半群 M] [模 R M]
  公理与运算 (1 个):
    - of_fg_top : : fg_top : (⊤ : 子模 R M).FG
-/
protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  of_fg_top ::
    fg_top : (⊤ : Submodule R M).FG

attribute [inherit_doc Module.Finite] Module.Finite.fg_top

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/--
theorem `finite_def` / 定理 `finite_def`

English:
theorem finite_def
  given: {R M} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: ⟨(·.fg_top), .of_fg_top⟩

中文:
定理 finite_def
  条件: {R M} [半环 R] [加法交换幺半群 M] [模 R M]
  证明: ⟨(·.fg_top), .of_fg_top⟩

Depends on / 依赖: fg_top, of_fg_top
-/
theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module.Finite R M ↔ (⊤ : Submodule R M).FG :=
  ⟨(·.fg_top), .of_fg_top⟩

namespace Finite

open Submodule Set

/--
theorem `iff_addMonoid_fg` / 定理 `iff_addMonoid_fg`

English:
theorem iff_addMonoid_fg
  given: {M : Type*} [AddCommMonoid M]
  statement: Module.Finite Nat M ↔ AddMonoid.FG M
  proof: ⟨fun h => AddMonoid.fg_def.mpr (fg_iff_addSubmonoid_fg ⊤).mp h.fg_top,
fun h => of_fg_top (fg_iff_addSubmonoid_fg ⊤).mpr (AddMonoid.fg_def.mp h)⟩

中文:
定理 iff_addMonoid_fg
  条件: {M : 类型} [加法交换幺半群 M]
  结论: 模.有限 自然数 M ↔ 加法幺半群.FG M
  证明: ⟨fun h => AddMonoid.fg_def.mpr (fg_iff_addSubmonoid_fg ⊤).mp h.fg_top,
fun h => of_fg_top (fg_iff_addSubmonoid_fg ⊤).mpr (AddMonoid.fg_def.mp h)⟩

Depends on / 依赖: AddMonoid, AddMonoid.fg_def.mp, AddMonoid.fg_def.mpr, fg_def, fg_iff_addSubmonoid_fg, fg_top, h.fg_top, of_fg_top
-/
theorem iff_addMonoid_fg {M : Type*} [AddCommMonoid M] : Module.Finite Nat M ↔ AddMonoid.FG M :=
⟨fun h => AddMonoid.fg_def.mpr (fg_iff_addSubmonoid_fg ⊤).mp h.fg_top,
fun h => of_fg_top (fg_iff_addSubmonoid_fg ⊤).mpr (AddMonoid.fg_def.mp h)⟩

/--
theorem `iff_addGroup_fg` / 定理 `iff_addGroup_fg`

English:
theorem iff_addGroup_fg
  given: {G : Type*} [AddCommGroup G]
  statement: Module.Finite Int G ↔ AddGroup.FG G
  proof: ⟨fun h => AddGroup.fg_def.mpr (fg_iff_addSubgroup_fg ⊤).mp h.fg_top,
fun h => of_fg_top (fg_iff_addSubgroup_fg ⊤).mpr (AddGroup.fg_def.mp h)⟩

中文:
定理 iff_addGroup_fg
  条件: {G : 类型} [加法交换群 G]
  结论: 模.有限 整数 G ↔ 加法群.FG G
  证明: ⟨fun h => AddGroup.fg_def.mpr (fg_iff_addSubgroup_fg ⊤).mp h.fg_top,
fun h => of_fg_top (fg_iff_addSubgroup_fg ⊤).mpr (AddGroup.fg_def.mp h)⟩

Depends on / 依赖: AddGroup, AddGroup.fg_def.mp, AddGroup.fg_def.mpr, fg_def, fg_iff_addSubgroup_fg, fg_top, h.fg_top, of_fg_top
-/
theorem iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite Int G ↔ AddGroup.FG G :=
⟨fun h => AddGroup.fg_def.mpr (fg_iff_addSubgroup_fg ⊤).mp h.fg_top,
fun h => of_fg_top (fg_iff_addSubgroup_fg ⊤).mpr (AddGroup.fg_def.mp h)⟩

variable {R M N}

/--
lemma `exists_fin` / 引理 `exists_fin`

English:
lemma exists_fin
  given: [Module.Finite R M]
  statement: exists (n : Nat) (s : Fin n -> M), span R (range s) = ⊤
  proof: fg_iff_exists_fin_generating_family.mp fg_top

中文:
引理 存在_fin
  条件: [模.有限 R M]
  结论: 存在 (n : 自然数) (s : 有限集 n -> M), span R (range s) = ⊤
  证明: fg_iff_exists_fin_generating_family.mp fg_top

Depends on / 依赖: fg_iff_exists_fin_generating_family, fg_iff_exists_fin_generating_family.mp, fg_top
-/
lemma exists_fin [Module.Finite R M] : exists (n : Nat) (s : Fin n -> M), span R (range s) = ⊤ :=
  fg_iff_exists_fin_generating_family.mp fg_top

end Finite

end Module

/--
Instance `AddMonoid.FG.to_moduleFinite_nat` / 实例 `AddMonoid.FG.to_moduleFinite_nat`

English:
instance AddMonoid.FG.to_moduleFinite_nat
  signature: {M : Type*} [AddCommMonoid M] [FG M]
  body: Module.Finite.iff_addMonoid_fg.mpr ‹_›

中文:
实例 加法幺半群.FG.to_moduleFinite_nat
  签名: {M : 类型} [加法交换幺半群 M] [FG M]
  定义体: Module.Finite.iff_addMonoid_fg.mpr ‹_›

Depends on / 依赖: Finite, Module, Module.Finite.iff_addMonoid_fg.mpr, iff_addMonoid_fg
-/
instance AddMonoid.FG.to_moduleFinite_nat {M : Type*} [AddCommMonoid M] [FG M] :
    Module.Finite Nat M :=
  Module.Finite.iff_addMonoid_fg.mpr ‹_›

/--
Instance `AddMonoid.FG.to_moduleFinite_int` / 实例 `AddMonoid.FG.to_moduleFinite_int`

English:
instance AddMonoid.FG.to_moduleFinite_int
  signature: {G : Type*} [AddCommGroup G] [FG G]
  body: Module.Finite.iff_addGroup_fg.mpr AddGroup.fg_iff_addMonoid_fg.mpr ‹_›

中文:
实例 加法幺半群.FG.to_moduleFinite_int
  签名: {G : 类型} [加法交换群 G] [FG G]
  定义体: Module.Finite.iff_addGroup_fg.mpr AddGroup.fg_iff_addMonoid_fg.mpr ‹_›

Depends on / 依赖: AddGroup, AddGroup.fg_iff_addMonoid_fg.mpr, Finite, Module, Module.Finite.iff_addGroup_fg.mpr, fg_iff_addMonoid_fg, iff_addGroup_fg
-/
instance AddMonoid.FG.to_moduleFinite_int {G : Type*} [AddCommGroup G] [FG G] :
    Module.Finite Int G :=
Module.Finite.iff_addGroup_fg.mpr AddGroup.fg_iff_addMonoid_fg.mpr ‹_›

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `RingHom.Finite` if `B` is finitely generated as `A`-module. -/
@[algebraize Module.Finite, stacks 0563]
/--
Definition of `Finite` / `Finite` 的定义

English:
definition Finite
  signature: (f : A ->+* B)
  body: letI : Algebra A B := f.toAlgebra
  Module.Finite A B

@[simp]

中文:
定义 有限
  签名: (f : A ->+* B)
  定义体: letI : Algebra A B := f.toAlgebra
  Module.Finite A B

@[simp]

Depends on / 依赖: Algebra, Finite, Module, Module.Finite, f.toAlgebra, toAlgebra
-/
def Finite (f : A ->+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B

@[simp]
/--
lemma `finite_algebraMap` / 引理 `finite_algebraMap`

English:
lemma finite_algebraMap
  given: [Algebra A B]
  proof: by
  rw [Finite]; rw [toAlgebra_algebraMap]

中文:
引理 finite_algebraMap
  条件: [代数 A B]
  证明: by
  rw [Finite]; rw [toAlgebra_algebraMap]

Depends on / 依赖: Finite, toAlgebra_algebraMap
-/
lemma finite_algebraMap [Algebra A B] :
    (algebraMap A B).Finite ↔ Module.Finite A B := by
  rw [Finite]; rw [toAlgebra_algebraMap]

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/--
Definition of `Finite` / `Finite` 的定义

English:
definition Finite
  signature: (f : A ->ₐ[R] B)
  body: f.toRingHom.Finite

中文:
定义 有限
  签名: (f : A ->ₐ[R] B)
  定义体: f.toRingHom.Finite

Depends on / 依赖: Finite, f.toRingHom.Finite, toRingHom
-/
def Finite (f : A ->ₐ[R] B) : Prop :=
  f.toRingHom.Finite

end AlgHom
