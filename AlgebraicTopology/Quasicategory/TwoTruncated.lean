/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

/-!
# 2-truncated quasicategories and homotopy relations

We define 2-truncated quasicategories `Quasicategory₂` by three horn-filling properties,
and the left and right homotopy relations `HomotopicL` and `HomotopicR` on the edges in a
2-truncated simplicial set.

We prove that for 2-truncated quasicategories, both homotopy relations are equivalence
relations, and that the left and right homotopy relations coincide.

For a 2-truncated quasicategory `A`, we define a category `HomotopyCategory₂ A` whose
morphisms are given by (left) homotopy classes of edges. The construction of this category
is different from `HomotopyCategory A` in `AlgebraicTopology.SimplicialSet.HomotopyCat`:
* `HomotopyCategory₂ A` has morphisms given by homotopy classes of edges
* `HomotopyCategory A` has morphisms given by equivalence classes of paths in the underlying
  reflexive quiver of `A`.

The two constructions agree for 2-truncated quasicategories (TODO: handled by future PR).

## Implementation notes

Throughout this file, we make use of `Edge` and `CompStruct` to conveniently deal with
edges and triangles in a 2-truncated simplicial set.
-/

@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated
open Edge CompStruct

/--
Definition of `Quasicategory₂` / `Quasicategory₂` 的定义

English:
class Quasicategory₂
  parameters: (X : Truncated 2)
  axioms and operations (3):
    - fill21({x₀ x₁ x₂ : X _⦋0⦌₂} (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)) : Nonempty (Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂)
    - fill31({x₀ x₁ x₂ x₃ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃} {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃} (f₃ : CompStruct e₀₁ e₁₂ e₀₂) (f₀ : CompStruct e₁₂ e₂₃ e₁₃) (f₂ : CompStruct e₀₁ e₁₃ e₀₃)) : Nonempty (CompStruct e₀₂ e₂₃ e₀₃)
    - fill32({x₀ x₁ x₂ x₃ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃} {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃} (f₃ : CompStruct e₀₁ e₁₂ e₀₂) (f₀ : CompStruct e₁₂ e₂₃ e₁₃) (f₁ : CompStruct e₀₂ e₂₃ e₀₃)) : Nonempty (CompStruct e₀₁ e₁₃ e₀₃)

中文:
类 Quasicategory₂
  参数: (X : Truncated 2)
  公理与运算 (3 个):
    - fill21({x₀ x₁ x₂ : X _⦋0⦌₂} (e₀₁ : 边 x₀ x₁) (e₁₂ : 边 x₁ x₂)) : 非空 (Σ e₀₂ : 边 x₀ x₂, 余mpStruct e₀₁ e₁₂ e₀₂)
    - fill31({x₀ x₁ x₂ x₃ : X _⦋0⦌₂} {e₀₁ : 边 x₀ x₁} {e₁₂ : 边 x₁ x₂} {e₂₃ : 边 x₂ x₃} {e₀₂ : 边 x₀ x₂} {e₁₃ : 边 x₁ x₃} {e₀₃ : 边 x₀ x₃} (f₃ : 余mpStruct e₀₁ e₁₂ e₀₂) (f₀ : 余mpStruct e₁₂ e₂₃ e₁₃) (f₂ : 余mpStruct e₀₁ e₁₃ e₀₃)) : 非空 (余mpStruct e₀₂ e₂₃ e₀₃)
    - fill32({x₀ x₁ x₂ x₃ : X _⦋0⦌₂} {e₀₁ : 边 x₀ x₁} {e₁₂ : 边 x₁ x₂} {e₂₃ : 边 x₂ x₃} {e₀₂ : 边 x₀ x₂} {e₁₃ : 边 x₁ x₃} {e₀₃ : 边 x₀ x₃} (f₃ : 余mpStruct e₀₁ e₁₂ e₀₂) (f₀ : 余mpStruct e₁₂ e₂₃ e₁₃) (f₁ : 余mpStruct e₀₂ e₂₃ e₀₃)) : 非空 (余mpStruct e₀₁ e₁₃ e₀₃)
-/
class Quasicategory₂ (X : Truncated 2) where
  fill21 {x₀ x₁ x₂ : X _⦋0⦌₂}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
      Nonempty (Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂)
  fill31 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₂ : CompStruct e₀₁ e₁₃ e₀₃) :
      Nonempty (CompStruct e₀₂ e₂₃ e₀₃)
  fill32 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₁ : CompStruct e₀₂ e₂₃ e₀₃) :
      Nonempty (CompStruct e₀₁ e₁₃ e₀₃)

/--
Definition of `HomotopicL` / `HomotopicL` 的定义

English:
abbreviation HomotopicL
  signature: {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y)
  body: Nonempty (CompStruct f (id y) g)

中文:
缩写 HomotopicL
  签名: {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : 边 x y)
  定义体: Nonempty (CompStruct f (id y) g)

Depends on / 依赖: CompStruct, Nonempty
-/
abbrev HomotopicL {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct f (id y) g)

/--
Definition of `HomotopicR` / `HomotopicR` 的定义

English:
abbreviation HomotopicR
  signature: {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y)
  body: Nonempty (CompStruct (id x) f g)

中文:
缩写 HomotopicR
  签名: {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : 边 x y)
  定义体: Nonempty (CompStruct (id x) f g)

Depends on / 依赖: CompStruct, Nonempty
-/
abbrev HomotopicR {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct (id x) f g)

section homotopy_eqrel
variable {X : Truncated 2}

/--
lemma `HomotopicL.refl` / 引理 `HomotopicL.refl`

English:
lemma HomotopicL.refl
  given: {x y : X _⦋0⦌₂} {f : Edge x y}
  statement: HomotopicL f f
  proof: ⟨compId f⟩

中文:
引理 HomotopicL.refl
  条件: {x y : X _⦋0⦌₂} {f : 边 x y}
  结论: HomotopicL f f
  证明: ⟨compId f⟩

Depends on / 依赖: compId
-/
lemma HomotopicL.refl {x y : X _⦋0⦌₂} {f : Edge x y} : HomotopicL f f := ⟨compId f⟩

/--
lemma `HomotopicL.symm` / 引理 `HomotopicL.symm`

English:
lemma HomotopicL.symm
  given: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g)
  proof: by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idComp (id y)) (compId f)

中文:
引理 HomotopicL.symm
  条件: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : 边 x y} (hfg : HomotopicL f g)
  证明: by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idComp (id y)) (compId f)

Depends on / 依赖: compId, fill31, idComp
-/
lemma HomotopicL.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idComp (id y)) (compId f)

/--
lemma `HomotopicL.trans` / 引理 `HomotopicL.trans`

English:
lemma HomotopicL.trans
  statement: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
  proof: by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idComp (id y)) hgh

中文:
引理 HomotopicL.trans
  结论: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : 边 x y} (hfg : HomotopicL f g)
  证明: by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idComp (id y)) hgh

Depends on / 依赖: fill32, idComp
-/
lemma HomotopicL.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) : HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idComp (id y)) hgh

/--
lemma `HomotopicR.refl` / 引理 `HomotopicR.refl`

English:
lemma HomotopicR.refl
  given: {x y : X _⦋0⦌₂} {f : Edge x y}
  statement: HomotopicR f f
  proof: ⟨idComp f⟩

中文:
引理 HomotopicR.refl
  条件: {x y : X _⦋0⦌₂} {f : 边 x y}
  结论: HomotopicR f f
  证明: ⟨idComp f⟩

Depends on / 依赖: idComp
-/
lemma HomotopicR.refl {x y : X _⦋0⦌₂} {f : Edge x y} : HomotopicR f f := ⟨idComp f⟩

/--
lemma `HomotopicR.symm` / 引理 `HomotopicR.symm`

English:
lemma HomotopicR.symm
  given: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g)
  proof: by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idComp (id x)) hfg (idComp f)

中文:
引理 HomotopicR.symm
  条件: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : 边 x y} (hfg : HomotopicR f g)
  证明: by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idComp (id x)) hfg (idComp f)

Depends on / 依赖: fill32, idComp
-/
lemma HomotopicR.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idComp (id x)) hfg (idComp f)

/--
lemma `HomotopicR.trans` / 引理 `HomotopicR.trans`

English:
lemma HomotopicR.trans
  statement: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
  proof: by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idComp (id x)) hfg hgh

中文:
引理 HomotopicR.trans
  结论: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : 边 x y} (hfg : HomotopicR f g)
  证明: by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idComp (id x)) hfg hgh

Depends on / 依赖: fill31, idComp
-/
lemma HomotopicR.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) : HomotopicR f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idComp (id x)) hfg hgh

/--
lemma `HomotopicL.homotopicR` / 引理 `HomotopicL.homotopicR`

English:
lemma HomotopicL.homotopicR
  statement: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
  proof: by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill32 (idComp f) (compId f) h

中文:
引理 HomotopicL.homotopicR
  结论: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : 边 x y}
  证明: by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill32 (idComp f) (compId f) h

Depends on / 依赖: compId, fill32, idComp
-/
lemma HomotopicL.homotopicR [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicL f g) : HomotopicR f g := by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill32 (idComp f) (compId f) h

/--
lemma `HomotopicR.homotopicL` / 引理 `HomotopicR.homotopicL`

English:
lemma HomotopicR.homotopicL
  statement: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
  proof: by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill31 (idComp f) (compId f) h

中文:
引理 HomotopicR.homotopicL
  结论: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : 边 x y}
  证明: by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill31 (idComp f) (compId f) h

Depends on / 依赖: compId, fill31, idComp
-/
lemma HomotopicR.homotopicL [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicR f g) : HomotopicL f g := by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill31 (idComp f) (compId f) h

/--
theorem `homotopicL_iff_homotopicR` / 定理 `homotopicL_iff_homotopicR`

English:
theorem homotopicL_iff_homotopicR
  given: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
  proof: ⟨HomotopicL.homotopicR, HomotopicR.homotopicL⟩

中文:
定理 homotopicL_iff_homotopicR
  条件: [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : 边 x y}
  证明: ⟨HomotopicL.homotopicR, HomotopicR.homotopicL⟩

Depends on / 依赖: HomotopicL, HomotopicL.homotopicR, HomotopicR, HomotopicR.homotopicL, homotopicL, homotopicR
-/
theorem homotopicL_iff_homotopicR [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} :
    HomotopicL f g ↔ HomotopicR f g :=
  ⟨HomotopicL.homotopicR, HomotopicR.homotopicL⟩

end homotopy_eqrel

section homotopy_category

variable {A : Truncated 2} [Quasicategory₂ A] {x y z : A _⦋0⦌₂}

/--
lemma `Edge.CompStruct.comp_unique` / 引理 `Edge.CompStruct.comp_unique`

English:
lemma Edge.CompStruct.comp_unique
  statement: {f f' : Edge x y} {g g' : Edge y z} {h h' : Edge x z}
  proof: by
  rcases hg.homotopicR with ⟨hg⟩
  rcases hf with ⟨hf⟩
  let ⟨s₁⟩ := Quasicategory₂.fill32 hf (idComp g') s'
  let ⟨s₂⟩ := Quasicategory₂.fill31 (compId f) hg s₁
  exact Quasicategory₂.fill31 s (compId g) s₂

中文:
引理 边.余mpStruct.comp_unique
  结论: {f f' : 边 x y} {g g' : 边 y z} {h h' : 边 x z}
  证明: by
  rcases hg.homotopicR with ⟨hg⟩
  rcases hf with ⟨hf⟩
  let ⟨s₁⟩ := Quasicategory₂.fill32 hf (idComp g') s'
  let ⟨s₂⟩ := Quasicategory₂.fill31 (compId f) hg s₁
  exact Quasicategory₂.fill31 s (compId g) s₂

Depends on / 依赖: compId, fill31, fill32, hg.homotopicR, homotopicR, idComp
-/
lemma Edge.CompStruct.comp_unique {f f' : Edge x y} {g g' : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (s' : CompStruct f' g' h')
    (hf : HomotopicL f f') (hg : HomotopicL g g') : HomotopicL h h' := by
  rcases hg.homotopicR with ⟨hg⟩
  rcases hf with ⟨hf⟩
  let ⟨s₁⟩ := Quasicategory₂.fill32 hf (idComp g') s'
  let ⟨s₂⟩ := Quasicategory₂.fill31 (compId f) hg s₁
  exact Quasicategory₂.fill31 s (compId g) s₂

/--
Definition of `Edge.comp` / `Edge.comp` 的定义

English:
definition Edge.comp
  signature: (f : Edge x y) (g : Edge y z)
  body: (Quasicategory₂.fill21 f g).some.1

中文:
定义 边.comp
  签名: (f : 边 x y) (g : 边 y z)
  定义体: (Quasicategory₂.fill21 f g).some.1

Depends on / 依赖: fill21
-/
noncomputable def Edge.comp (f : Edge x y) (g : Edge y z) : Edge x z :=
  (Quasicategory₂.fill21 f g).some.1

/--
Definition of `Edge.compStruct` / `Edge.compStruct` 的定义

English:
definition Edge.compStruct
  signature: (f : Edge x y) (g : Edge y z)
  body: (Quasicategory₂.fill21 f g).some.2

中文:
定义 边.compStruct
  签名: (f : 边 x y) (g : 边 y z)
  定义体: (Quasicategory₂.fill21 f g).some.2

Depends on / 依赖: fill21
-/
noncomputable def Edge.compStruct (f : Edge x y) (g : Edge y z) : CompStruct f g (f.comp g) :=
  (Quasicategory₂.fill21 f g).some.2

/--
Definition of `HomotopyCategory₂` / `HomotopyCategory₂` 的定义

English:
structure HomotopyCategory₂
  parameters: (A : Truncated 2)
  axioms and operations (1):
    - pt : A _⦋0⦌₂

中文:
结构 HomotopyCategory₂
  参数: (A : Truncated 2)
  公理与运算 (1 个):
    - pt : A _⦋0⦌₂
-/
structure HomotopyCategory₂ (A : Truncated 2) where
  /-- An object of the homotopy category is a vertex of `A`. -/
  pt : A _⦋0⦌₂

/--
Instance `instSetoidEdge` / 实例 `instSetoidEdge`

English:
instance instSetoidEdge
  signature: (x y : A _⦋0⦌₂)
  body: HomotopicL
  iseqv := ⟨fun _ => HomotopicL.refl, HomotopicL.symm, HomotopicL.trans⟩

中文:
实例 instSetoidEdge
  签名: (x y : A _⦋0⦌₂)
  定义体: HomotopicL
  iseqv := ⟨fun _ => HomotopicL.refl, HomotopicL.symm, HomotopicL.trans⟩

Depends on / 依赖: HomotopicL
-/
instance instSetoidEdge (x y : A _⦋0⦌₂) : Setoid (Edge x y) where
  r := HomotopicL
  iseqv := ⟨fun _ => HomotopicL.refl, HomotopicL.symm, HomotopicL.trans⟩

namespace HomotopyCategory₂

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: (x y : HomotopyCategory₂ A)
  body: Quotient (instSetoidEdge x.pt y.pt)

中文:
定义 态射
  签名: (x y : HomotopyCategory₂ A)
  定义体: Quotient (instSetoidEdge x.pt y.pt)

Depends on / 依赖: Quotient, instSetoidEdge, x.pt, y.pt
-/
def Hom (x y : HomotopyCategory₂ A) := Quotient (instSetoidEdge x.pt y.pt)

/--
Composition of morphisms in `HomotopyCategory₂ A` is given by lifting the edge
chosen by `composeEdges`.
-/
noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (HomotopyCategory₂ A)
  body: Hom x y
  id x := Quotient.mk' (Edge.id x.pt)
  comp := Quotient.lift₂ (fun f g => ⟦comp f g⟧)
    (fun _ _ _ _ hf hg => Quotient.sound
      (Edge.CompStruct.comp_unique (compStruct _ _) (compStruct _ _) hf hg))

omit [A.Quasicategory₂] in

中文:
实例 :
  签名: CategoryStruct (HomotopyCategory₂ A)
  定义体: Hom x y
  id x := Quotient.mk' (Edge.id x.pt)
  comp := Quotient.lift₂ (fun f g => ⟦comp f g⟧)
    (fun _ _ _ _ hf hg => Quotient.sound
      (Edge.CompStruct.comp_unique (compStruct _ _) (compStruct _ _) hf hg))

omit [A.Quasicategory₂] in
-/
instance : CategoryStruct (HomotopyCategory₂ A) where
  Hom x y := Hom x y
  id x := Quotient.mk' (Edge.id x.pt)
  comp := Quotient.lift₂ (fun f g => ⟦comp f g⟧)
    (fun _ _ _ _ hf hg => Quotient.sound
      (Edge.CompStruct.comp_unique (compStruct _ _) (compStruct _ _) hf hg))

omit [A.Quasicategory₂] in
/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (mk : A _⦋0⦌₂ -> _)
  proof: fun ⟨x⟩ => ⟨x, rfl⟩

中文:
引理 mk_surjective
  结论: 函数.满射 (mk : A _⦋0⦌₂ -> _)
  证明: fun ⟨x⟩ => ⟨x, rfl⟩
-/
lemma mk_surjective : Function.Surjective (mk : A _⦋0⦌₂ -> _) :=
  fun ⟨x⟩ => ⟨x, rfl⟩

/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: (f : Edge x y)
  body: ⟦f⟧

中文:
定义 homMk
  签名: (f : 边 x y)
  定义体: ⟦f⟧
-/
def homMk (f : Edge x y) : mk x ⟶ mk y := ⟦f⟧

/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  statement: Function.Surjective (homMk : Edge x y -> _)
  proof: Quotient.mk_surjective

中文:
引理 homMk_surjective
  结论: 函数.满射 (homMk : 边 x y -> _)
  证明: Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective
-/
lemma homMk_surjective : Function.Surjective (homMk : Edge x y -> _) := Quotient.mk_surjective

/--
The trivial (degenerate) edge at a vertex `x` is a representative for the
identity morphism `x ⟶ x`.
-/
@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (x : HomotopyCategory₂ A)
  statement: homMk (Edge.id x.pt) = 𝟙 x
  proof: rfl

中文:
引理 homMk_id
  条件: (x : HomotopyCategory₂ A)
  结论: homMk (边.id x.pt) = 𝟙 x
  证明: rfl
-/
lemma homMk_id (x : HomotopyCategory₂ A) : homMk (Edge.id x.pt) = 𝟙 x := rfl

end HomotopyCategory₂

open HomotopyCategory₂

/--
lemma `HomotopicL.congr_homotopyCategory₂HomMk` / 引理 `HomotopicL.congr_homotopyCategory₂HomMk`

English:
lemma HomotopicL.congr_homotopyCategory₂HomMk
  given: {f g : Edge x y} (h : HomotopicL f g)
  proof: Quotient.sound h

中文:
引理 HomotopicL.congr_homotopyCategory₂HomMk
  条件: {f g : 边 x y} (h : HomotopicL f g)
  证明: Quotient.sound h

Depends on / 依赖: Quotient, Quotient.sound
-/
lemma HomotopicL.congr_homotopyCategory₂HomMk {f g : Edge x y} (h : HomotopicL f g) :
    homMk f = homMk g := Quotient.sound h

/--
lemma `HomotopicR.congr_homotopyCategory₂HomMk` / 引理 `HomotopicR.congr_homotopyCategory₂HomMk`

English:
lemma HomotopicR.congr_homotopyCategory₂HomMk
  given: {f g : Edge x y} (h : HomotopicR f g)
  proof: Quotient.sound h.homotopicL

中文:
引理 HomotopicR.congr_homotopyCategory₂HomMk
  条件: {f g : 边 x y} (h : HomotopicR f g)
  证明: Quotient.sound h.homotopicL

Depends on / 依赖: Quotient, Quotient.sound, h.homotopicL, homotopicL
-/
lemma HomotopicR.congr_homotopyCategory₂HomMk {f g : Edge x y} (h : HomotopicR f g) :
    homMk f = homMk g := Quotient.sound h.homotopicL

/--
lemma `Edge.CompStruct.homotopyCategory₂_fac` / 引理 `Edge.CompStruct.homotopyCategory₂_fac`

English:
lemma Edge.CompStruct.homotopyCategory₂_fac
  statement: {f : Edge x y} {g : Edge y z} {h : Edge x z}
  proof: (comp_unique (compStruct _ _) s .refl .refl).congr_homotopyCategory₂HomMk

中文:
引理 边.余mpStruct.homotopyCategory₂_fac
  结论: {f : 边 x y} {g : 边 y z} {h : 边 x z}
  证明: (comp_unique (compStruct _ _) s .refl .refl).congr_homotopyCategory₂HomMk

Depends on / 依赖: compStruct, comp_unique
-/
lemma Edge.CompStruct.homotopyCategory₂_fac {f : Edge x y} {g : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) : homMk f ≫ homMk g = homMk h :=
  (comp_unique (compStruct _ _) s .refl .refl).congr_homotopyCategory₂HomMk

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Edge.CompStruct.ofHomotopyCategory₂Fac` / `Edge.CompStruct.ofHomotopyCategory₂Fac` 的定义

English:
definition Edge.CompStruct.ofHomotopyCategory₂Fac
  body: by
  dsimp [homMk, CategoryStruct.comp] at fac
  rw [Quotient.eq_iff_equiv] at fac
  exact (Quasicategory₂.fill32 (compStruct f g) (compId g) fac.some).some

中文:
定义 边.余mpStruct.ofHomotopyCategory₂Fac
  定义体: by
  dsimp [homMk, CategoryStruct.comp] at fac
  rw [Quotient.eq_iff_equiv] at fac
  exact (Quasicategory₂.fill32 (compStruct f g) (compId g) fac.some).some

Depends on / 依赖: CategoryStruct, CategoryStruct.comp, Quotient, Quotient.eq_iff_equiv, compId, compStruct, eq_iff_equiv, fac.some, fill32
-/
noncomputable def Edge.CompStruct.ofHomotopyCategory₂Fac
    {f : Edge x y} {g : Edge y z} {h : Edge x z}
    (fac : homMk f ≫ homMk g = homMk h) : CompStruct f g h := by
  dsimp [homMk, CategoryStruct.comp] at fac
  rw [Quotient.eq_iff_equiv] at fac
  exact (Quasicategory₂.fill32 (compStruct f g) (compId g) fac.some).some

/--
lemma `Edge.CompStruct.nonempty_iff` / 引理 `Edge.CompStruct.nonempty_iff`

English:
lemma Edge.CompStruct.nonempty_iff
  given: {f : Edge x y} {g : Edge y z} {h : Edge x z}
  proof: ⟨fun ⟨h⟩ => h.homotopyCategory₂_fac, fun h => ⟨.ofHomotopyCategory₂Fac h⟩⟩

noncomputable

中文:
引理 边.余mpStruct.nonempty_iff
  条件: {f : 边 x y} {g : 边 y z} {h : 边 x z}
  证明: ⟨fun ⟨h⟩ => h.homotopyCategory₂_fac, fun h => ⟨.ofHomotopyCategory₂Fac h⟩⟩

noncomputable

Depends on / 依赖: h.homotopyCategory
-/
lemma Edge.CompStruct.nonempty_iff {f : Edge x y} {g : Edge y z} {h : Edge x z} :
    Nonempty (CompStruct f g h) ↔ homMk f ≫ homMk g = homMk h :=
  ⟨fun ⟨h⟩ => h.homotopyCategory₂_fac, fun h => ⟨.ofHomotopyCategory₂Fac h⟩⟩

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (HomotopyCategory₂ A)
  body: by
    rintro _ _ ⟨f⟩
    exact ((compStruct _ f).comp_unique (idComp _) .refl .refl).congr_homotopyCategory₂HomMk
  comp_id := by
    rintro _ _ ⟨f⟩
    exact ((compStruct _ _).comp_unique (compId _) .refl .refl).congr_homotopyCategory₂HomMk
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact (Q

中文:
实例 :
  签名: 范畴 (HomotopyCategory₂ A)
  定义体: by
    rintro _ _ ⟨f⟩
    exact ((compStruct _ f).comp_unique (idComp _) .refl .refl).congr_homotopyCategory₂HomMk
  comp_id := by
    rintro _ _ ⟨f⟩
    exact ((compStruct _ _).comp_unique (compId _) .refl .refl).congr_homotopyCategory₂HomMk
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact (Q

Depends on / 依赖: compId, compStruct, comp_id, comp_unique, fill31, idComp, some.homotopyCategory
-/
instance : Category (HomotopyCategory₂ A) where
  id_comp := by
    rintro _ _ ⟨f⟩
    exact ((compStruct _ f).comp_unique (idComp _) .refl .refl).congr_homotopyCategory₂HomMk
  comp_id := by
    rintro _ _ ⟨f⟩
    exact ((compStruct _ _).comp_unique (compId _) .refl .refl).congr_homotopyCategory₂HomMk
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact (Quasicategory₂.fill31 (compStruct f g) (compStruct g h)
      (compStruct _ _)).some.homotopyCategory₂_fac

end homotopy_category

end SSet.Truncated
