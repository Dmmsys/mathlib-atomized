/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Locality conditions on object properties

In this file we define locality conditions on object properties in a category. Let `K` be a
precoverage in a category `C` and `P` be an object property that is closed under isomorphisms.

We say that

- `P` is local if for every `X : C`, `P` holds for `X` if and only if it holds for `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `X`.

## Implementation details

The covers appearing in the definitions have index type in the morphism universe of `C`.
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/--
Definition of `IsLocal` / `IsLocal` 的定义

English:
class IsLocal
  parameters: (P : ObjectProperty C) (K : Precoverage C)
  extends: IsClosedUnderIsomorphisms P
  axioms and operations (2):
    - component({X : C} {R : Presieve X} (hR : R in K X) {Y : C} (f : Y ⟶ X) (hf : R f)) : P X -> P Y
    - of_presieve({X : C} {R : Presieve X} (hR : R in K X) (H : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f -> P Y)) : P X

中文:
类 是Local
  参数: (P : ObjectProperty C) (K : Precoverage C)
  继承: 在同构下封闭 P
  公理与运算 (2 个):
    - component({X : C} {R : Presieve X} (hR : R in K X) {Y : C} (f : Y ⟶ X) (hf : R f)) : P X -> P Y
    - of_presieve({X : C} {R : Presieve X} (hR : R in K X) (H : 对任意 ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f -> P Y)) : P X
-/
class IsLocal (P : ObjectProperty C) (K : Precoverage C) extends IsClosedUnderIsomorphisms P where
  component {X : C} {R : Presieve X} (hR : R in K X) {Y : C} (f : Y ⟶ X) (hf : R f) : P X -> P Y
  of_presieve {X : C} {R : Presieve X} (hR : R in K X) (H : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f -> P Y) : P X

export IsLocal (of_presieve)

variable {P : ObjectProperty C} {K L : Precoverage C}

/--
lemma `iff_of_presieve` / 引理 `iff_of_presieve`

English:
lemma iff_of_presieve
  given: [P.IsLocal K] {X : C} {R : Presieve X} (hR : R in K X)
  proof: ⟨fun h _ _ hf => IsLocal.component hR _ hf h, fun h => of_presieve hR h⟩

中文:
引理 iff_of_presieve
  条件: [P.是Local K] {X : C} {R : Presieve X} (hR : R in K X)
  证明: ⟨fun h _ _ hf => IsLocal.component hR _ hf h, fun h => of_presieve hR h⟩

Depends on / 依赖: IsLocal, IsLocal.component, component, of_presieve
-/
lemma iff_of_presieve [P.IsLocal K] {X : C} {R : Presieve X} (hR : R in K X) :
    P X ↔ forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f -> P Y :=
  ⟨fun h _ _ hf => IsLocal.component hR _ hf h, fun h => of_presieve hR h⟩

namespace IsLocal

/--
lemma `mk_of_zeroHypercover` / 引理 `mk_of_zeroHypercover`

English:
lemma mk_of_zeroHypercover
  statement: [P.IsClosedUnderIsomorphisms]
  proof: by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰] at hX
    obtain ⟨i⟩ := hf
    exact hX i
  of_presieve {X R} hR h := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰]
    intro i
    exact h ⟨i⟩

中文:
引理 mk_of_zeroHypercover
  结论: [P.在同构下封闭]
  证明: by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰] at hX
    obtain ⟨i⟩ := hf
    exact hX i
  of_presieve {X R} hR h := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰]
    intro i
    exact h ⟨i⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover, Precoverage, mem_iff_exists_zeroHypercover, of_presieve
-/
lemma mk_of_zeroHypercover [P.IsClosedUnderIsomorphisms]
    (H : forall ⦃X : C⦄ (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
      P X ↔ forall i, P (𝒰.X i)) :
    P.IsLocal K where
  component {X R} hR Y f hf hX := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰] at hX
    obtain ⟨i⟩ := hf
    exact hX i
  of_presieve {X R} hR h := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰]
    intro i
    exact h ⟨i⟩

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: [IsLocal P L] (hle : K <= L)
  statement: IsLocal P K where
  proof: component (hle _ hR) f hf hX
  of_presieve hR H := of_presieve (hle _ hR) H

中文:
引理 of_le
  条件: [是Local P L] (hle : K <= L)
  结论: 是Local P K where
  证明: component (hle _ hR) f hf hX
  of_presieve hR H := of_presieve (hle _ hR) H

Depends on / 依赖: component
-/
lemma of_le [IsLocal P L] (hle : K <= L) : IsLocal P K where
  component hR _ f hf hX := component (hle _ hR) f hf hX
  of_presieve hR H := of_presieve (hle _ hR) H

/--
Instance `top` / 实例 `top`

English:
instance top
  signature: : IsLocal (⊤ : ObjectProperty C) K where
  body: by simp
  of_presieve := by simp

中文:
实例 top
  签名: : 是Local (⊤ : ObjectProperty C) K where
  定义体: by simp
  of_presieve := by simp

Depends on / 依赖: of_presieve
-/
instance top : IsLocal (⊤ : ObjectProperty C) K where
  component := by simp
  of_presieve := by simp

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: (P Q : ObjectProperty C) [IsLocal P K] [IsLocal Q K]
  body: ⟨component hR _ hf h.1, component hR _ hf h.2⟩
  of_presieve hR h := ⟨of_presieve hR fun _ _ hf => (h hf).1, of_presieve hR fun _ _ hf => (h hf).2⟩

中文:
实例 下确界
  签名: (P Q : ObjectProperty C) [是Local P K] [是Local Q K]
  定义体: ⟨component hR _ hf h.1, component hR _ hf h.2⟩
  of_presieve hR h := ⟨of_presieve hR fun _ _ hf => (h hf).1, of_presieve hR fun _ _ hf => (h hf).2⟩

Depends on / 依赖: component
-/
instance inf (P Q : ObjectProperty C) [IsLocal P K] [IsLocal Q K] :
    IsLocal (P ⊓ Q) K where
  component hR _ _ hf h := ⟨component hR _ hf h.1, component hR _ hf h.2⟩
  of_presieve hR h := ⟨of_presieve hR fun _ _ hf => (h hf).1, of_presieve hR fun _ _ hf => (h hf).2⟩

end IsLocal

/--
lemma `of_zeroHypercover` / 引理 `of_zeroHypercover`

English:
lemma of_zeroHypercover
  given: [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) (h : forall i, P (𝒰.X i))
  statement: P X
  proof: P.of_presieve 𝒰.mem₀ fun _ f ⟨i⟩ => h i

中文:
引理 of_zeroHypercover
  条件: [P.是Local K] {X : C} (𝒰 : K.ZeroHypercover X) (h : 对任意 i, P (𝒰.X i))
  结论: P X
  证明: P.of_presieve 𝒰.mem₀ fun _ f ⟨i⟩ => h i

Depends on / 依赖: P.of_presieve, of_presieve
-/
lemma of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) (h : forall i, P (𝒰.X i)) : P X :=
  P.of_presieve 𝒰.mem₀ fun _ f ⟨i⟩ => h i

/--
lemma `iff_of_zeroHypercover` / 引理 `iff_of_zeroHypercover`

English:
lemma iff_of_zeroHypercover
  given: [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X)
  proof: ⟨fun h i => IsLocal.component 𝒰.mem₀ _ ⟨i⟩ h, fun h => of_zeroHypercover 𝒰 h⟩

中文:
引理 iff_of_zeroHypercover
  条件: [P.是Local K] {X : C} (𝒰 : K.ZeroHypercover X)
  证明: ⟨fun h i => IsLocal.component 𝒰.mem₀ _ ⟨i⟩ h, fun h => of_zeroHypercover 𝒰 h⟩

Depends on / 依赖: IsLocal, IsLocal.component, component, of_zeroHypercover
-/
lemma iff_of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) :
    P X ↔ forall i, P (𝒰.X i) :=
  ⟨fun h i => IsLocal.component 𝒰.mem₀ _ ⟨i⟩ h, fun h => of_zeroHypercover 𝒰 h⟩

end CategoryTheory.ObjectProperty
