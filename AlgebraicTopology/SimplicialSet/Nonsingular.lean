/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Nonsingular simplicial sets

In this file, we introduce a typeclass `SSet.Nonsingular` for a
simplicial set `X : SSet`: it says that for any non-degenerate simplex
`x : X _⦋n⦌`, the corresponding morphism `Δ[n] ⟶ X` is a monomorphism.
This notion is useful in the context of the study of the subdivision
functor (TODO @joelriou).

The condition `SSet.Nonsingular` is a weaker condition compared
to the notion of "polyhedral complex" which appears in the article
*Simplicial approximation* by Jardine, and which says that there
exists a monomorphism `X ⟶ nerve T` where `T` is a partially ordered type.

## References
* [Vegard Fjellbo and John Rognes,
  *Exponentials of non-singular simplicial sets*][fjellbo-rognes-2022]
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
/-- A simplicial set `X` is nonsingular if for any
nondegenerate simplex `x` (of dimension `n`), the corresponding
morphism `Δ[n] ⟶ X` is a monomorphism. -/
@[kerodon 02MG]
/--
Definition of `Nonsingular` / `Nonsingular` 的定义

English:
class Nonsingular
  parameters: where
  axioms and operations (1):
    - mono({n : Nat} (x : X.nonDegenerate n)) : Mono (yonedaEquiv.symm x.val)

中文:
类 Nonsingular
  参数: where
  公理与运算 (1 个):
    - mono({n : 自然数} (x : X.nonDegenerate n)) : Mono (yonedaEquiv.symm x.val)
-/
class Nonsingular where
  mono {n : Nat} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

attribute [instance] Nonsingular.mono

/--
lemma `Nonsingular.mono'` / 引理 `Nonsingular.mono'`

English:
lemma Nonsingular.mono'
  statement: [X.Nonsingular]
  proof: mono ⟨x, hx⟩

@[kerodon 02MK]

中文:
引理 Nonsingular.mono'
  结论: [X.Nonsingular]
  证明: mono ⟨x, hx⟩

@[kerodon 02MK]
-/
lemma Nonsingular.mono' [X.Nonsingular]
    {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) :
    Mono (yonedaEquiv.symm x) := mono ⟨x, hx⟩

@[kerodon 02MK]
/--
lemma `Nonsingular.of_mono` / 引理 `Nonsingular.of_mono`

English:
lemma Nonsingular.of_mono
  given: (f : X ⟶ Y) [Mono f] [Y.Nonsingular]
  proof: by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f

中文:
引理 Nonsingular.of_mono
  条件: (f : X ⟶ Y) [Mono f] [Y.Nonsingular]
  证明: by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f

Depends on / 依赖: SSet.yonedaEquiv_symm_comp, mono_of_mono, nonDegenerate_iff_of_mono, yonedaEquiv_symm_comp
-/
lemma Nonsingular.of_mono (f : X ⟶ Y) [Mono f] [Y.Nonsingular] :
    X.Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f

/--
lemma `Nonsingular.of_iso` / 引理 `Nonsingular.of_iso`

English:
lemma Nonsingular.of_iso
  given: (e : X ≅ Y) [X.Nonsingular]
  statement: Y.Nonsingular
  proof: .of_mono e.inv

中文:
引理 Nonsingular.of_iso
  条件: (e : X ≅ Y) [X.Nonsingular]
  结论: Y.Nonsingular
  证明: .of_mono e.inv

Depends on / 依赖: e.inv, of_mono
-/
lemma Nonsingular.of_iso (e : X ≅ Y) [X.Nonsingular] : Y.Nonsingular :=
  .of_mono e.inv

instance (A : X.Subcomplex) [X.Nonsingular] : (A : SSet).Nonsingular :=
  .of_mono A.ι

@[kerodon 02MT]
instance (T : Type*) [PartialOrder T] : (nerve T).Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective] at hx
    simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hx (Functor.congr_obj hij l)

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Nonsingular :=
  Nonsingular.of_iso (stdSimplex.isoNerve _).symm

instance (n m : SimplexCategory) :
    (stdSimplex.{u}.obj n otimes stdSimplex.obj m).Nonsingular :=
  Nonsingular.of_iso (prodStdSimplex.isoNerve _ _).symm

@[kerodon 02MH]
/--
lemma `nonDegenerate_δ` / 引理 `nonDegenerate_δ`

English:
lemma nonDegenerate_δ
  statement: [X.Nonsingular]
  proof: by
  have := Nonsingular.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this]; rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
  infer_instance

中文:
引理 nonDegenerate_δ
  结论: [X.Nonsingular]
  证明: by
  have := Nonsingular.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this]; rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
  infer_instance

Depends on / 依赖: Equiv.apply_symm_apply, Nonsingular, Nonsingular.mono, SimplexCategory, apply_symm_apply, infer_instance, mem_nonDegenerate_iff_mono, nonDegenerate_iff_of_mono, objEquiv, stdSimplex, stdSimplex.mem_nonDegenerate_iff_mono, stdSimplex.objEquiv.symm, yonedaEquiv, yonedaEquiv.symm
-/
lemma nonDegenerate_δ [X.Nonsingular]
    {n : Nat} {x : X _⦋n + 1⦌} (hx : x in X.nonDegenerate _) (i : Fin (n + 2)) :
    X.δ i x in X.nonDegenerate _ := by
  have := Nonsingular.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this]; rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
  infer_instance

/--
lemma `Nonsingular.δ_injective` / 引理 `Nonsingular.δ_injective`

English:
lemma Nonsingular.δ_injective
  statement: [X.Nonsingular]
  proof: by
  apply SimplexCategory.δ_injective
  apply stdSimplex.objEquiv.symm.injective
  have := mono' x hx
  exact injective_of_mono ((yonedaEquiv.symm x).app _) hij

中文:
引理 Nonsingular.δ_injective
  结论: [X.Nonsingular]
  证明: by
  apply SimplexCategory.δ_injective
  apply stdSimplex.objEquiv.symm.injective
  have := mono' x hx
  exact injective_of_mono ((yonedaEquiv.symm x).app _) hij

Depends on / 依赖: SimplexCategory, injective, injective_of_mono, objEquiv, stdSimplex, stdSimplex.objEquiv.symm.injective, yonedaEquiv, yonedaEquiv.symm
-/
lemma Nonsingular.δ_injective [X.Nonsingular]
    {n : Nat} (x : X _⦋n + 1⦌) (hx : x in X.nonDegenerate _)
    (i j : Fin (n + 2)) (hij : X.δ i x = X.δ j x) : i = j := by
  apply SimplexCategory.δ_injective
  apply stdSimplex.objEquiv.symm.injective
  have := mono' x hx
  exact injective_of_mono ((yonedaEquiv.symm x).app _) hij

/--
lemma `Nonsingular.injective_map` / 引理 `Nonsingular.injective_map`

English:
lemma Nonsingular.injective_map
  proof: by
  have := Nonsingular.mono' x hx
  apply stdSimplex.{u}.map_injective
  rw [← cancel_mono (yonedaEquiv.symm x)]
  apply yonedaEquiv.injective
  simpa [yonedaEquiv_comp, yonedaEquiv_map]

中文:
引理 Nonsingular.injective_map
  证明: by
  have := Nonsingular.mono' x hx
  apply stdSimplex.{u}.map_injective
  rw [← cancel_mono (yonedaEquiv.symm x)]
  apply yonedaEquiv.injective
  simpa [yonedaEquiv_comp, yonedaEquiv_map]

Depends on / 依赖: Nonsingular, Nonsingular.mono, cancel_mono, injective, map_injective, stdSimplex, yonedaEquiv, yonedaEquiv.injective, yonedaEquiv.symm, yonedaEquiv_comp, yonedaEquiv_map
-/
lemma Nonsingular.injective_map
    [X.Nonsingular] {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
    {m : SimplexCategory} {f g : m ⟶ ⦋n⦌}
    (h : X.map f.op x = X.map g.op x) :
    f = g := by
  have := Nonsingular.mono' x hx
  apply stdSimplex.{u}.map_injective
  rw [← cancel_mono (yonedaEquiv.symm x)]
  apply yonedaEquiv.injective
  simpa [yonedaEquiv_comp, yonedaEquiv_map]

/--
lemma `Nonsingular.isIso_toOfSimplex` / 引理 `Nonsingular.isIso_toOfSimplex`

English:
lemma Nonsingular.isIso_toOfSimplex
  statement: [X.Nonsingular]
  proof: by
  rw [Subcomplex.isIso_toOfSimplex_iff]
  exact Nonsingular.mono' x hx

中文:
引理 Nonsingular.isIso_toOfSimplex
  结论: [X.Nonsingular]
  证明: by
  rw [Subcomplex.isIso_toOfSimplex_iff]
  exact Nonsingular.mono' x hx

Depends on / 依赖: Nonsingular, Nonsingular.mono, Subcomplex, Subcomplex.isIso_toOfSimplex_iff, isIso_toOfSimplex_iff
-/
lemma Nonsingular.isIso_toOfSimplex [X.Nonsingular]
    {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) :
    IsIso (Subcomplex.toOfSimplex x) := by
  rw [Subcomplex.isIso_toOfSimplex_iff]
  exact Nonsingular.mono' x hx

/-- If `x : X _⦋n⦌` is a nondegenerate simplex of a nonsingular simplicial set,
this is the isomorphism `Δ[n] ≅ Subcomplex.ofSimplex x` induced by `x`. -/
@[expose, simps! hom]
/--
Definition of `Nonsingular.iso` / `Nonsingular.iso` 的定义

English:
definition Nonsingular.iso
  body: letI := Nonsingular.isIso_toOfSimplex x hx
  asIso (Subcomplex.toOfSimplex x)

中文:
定义 Nonsingular.iso
  定义体: letI := Nonsingular.isIso_toOfSimplex x hx
  asIso (Subcomplex.toOfSimplex x)

Depends on / 依赖: Nonsingular, Nonsingular.isIso_toOfSimplex, Subcomplex, Subcomplex.toOfSimplex, isIso_toOfSimplex, toOfSimplex
-/
noncomputable def Nonsingular.iso
    [X.Nonsingular] {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) :
    Δ[n] ≅ Subcomplex.ofSimplex x :=
  letI := Nonsingular.isIso_toOfSimplex x hx
  asIso (Subcomplex.toOfSimplex x)

namespace N

variable [X.Nonsingular] {x y z : X.N} (h : x <= y)

include h in
/--
lemma `existsUnique_of_le` / 引理 `existsUnique_of_le`

English:
lemma existsUnique_of_le
  proof: existsUnique_of_exists_of_unique (by
    obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h
    exact ⟨f, inferInstance, hf⟩) (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ => by
    exact Nonsingular.injective_map _ y.nonDegenerate (by rw [hf₁, hf₂]))

中文:
引理 existsUnique_of_le
  证明: existsUnique_of_exists_of_unique (by
    obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h
    exact ⟨f, inferInstance, hf⟩) (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ => by
    exact Nonsingular.injective_map _ y.nonDegenerate (by rw [hf₁, hf₂]))

Depends on / 依赖: Nonsingular, Nonsingular.injective_map, existsUnique_of_exists_of_unique, injective_map, le_iff_exists_mono, nonDegenerate, y.nonDegenerate
-/
lemma existsUnique_of_le :
    exists! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.1.2 = x.1.2 :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h
    exact ⟨f, inferInstance, hf⟩) (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ => by
    exact Nonsingular.injective_map _ y.nonDegenerate (by rw [hf₁, hf₂]))

/--
Definition of `monoOfLE` / `monoOfLE` 的定义

English:
definition monoOfLE
  signature: : ⦋x.dim⦌ ⟶ ⦋y.dim⦌
  body: (existsUnique_of_le h).exists.choose

中文:
定义 monoOfLE
  签名: : ⦋x.dim⦌ ⟶ ⦋y.dim⦌
  定义体: (existsUnique_of_le h).exists.choose

Depends on / 依赖: exists.choose, existsUnique_of_le
-/
noncomputable def monoOfLE : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (existsUnique_of_le h).exists.choose

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (monoOfLE h)
  body: (existsUnique_of_le h).exists.choose_spec.1

@[simp]

中文:
实例 :
  签名: Mono (monoOfLE h)
  定义体: (existsUnique_of_le h).exists.choose_spec.1

@[simp]

Depends on / 依赖: choose_spec, exists.choose_spec, existsUnique_of_le
-/
instance : Mono (monoOfLE h) :=
  (existsUnique_of_le h).exists.choose_spec.1

@[simp]
/--
lemma `map_monoOfLE` / 引理 `map_monoOfLE`

English:
lemma map_monoOfLE
  statement: X.map (monoOfLE h).op y.simplex = x.simplex
  proof: (existsUnique_of_le h).exists.choose_spec.2

@[reassoc, simp]

中文:
引理 map_monoOfLE
  结论: X.map (monoOfLE h).op y.simplex = x.simplex
  证明: (existsUnique_of_le h).exists.choose_spec.2

@[reassoc, simp]

Depends on / 依赖: choose_spec, exists.choose_spec, existsUnique_of_le
-/
lemma map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.simplex :=
  (existsUnique_of_le h).exists.choose_spec.2

@[reassoc, simp]
/--
lemma `stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex` / 引理 `stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex`

English:
lemma stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex
  proof: by
  rw [yonedaEquiv_symm_naturality_left]; rw [map_monoOfLE]

中文:
引理 stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex
  证明: by
  rw [yonedaEquiv_symm_naturality_left]; rw [map_monoOfLE]

Depends on / 依赖: map_monoOfLE, yonedaEquiv_symm_naturality_left
-/
lemma stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex :
    stdSimplex.map (monoOfLE h) ≫ yonedaEquiv.symm y.simplex =
      yonedaEquiv.symm x.simplex := by
  rw [yonedaEquiv_symm_naturality_left]; rw [map_monoOfLE]

/--
lemma `monoOfLE_eq_iff` / 引理 `monoOfLE_eq_iff`

English:
lemma monoOfLE_eq_iff
  given: (h : x <= y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g]
  proof: ⟨by rintro rfl; simp,
    fun h' => (existsUnique_of_le h).unique ⟨inferInstance, by simp⟩ ⟨inferInstance, h'⟩⟩

中文:
引理 monoOfLE_eq_iff
  条件: (h : x <= y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g]
  证明: ⟨by rintro rfl; simp,
    fun h' => (existsUnique_of_le h).unique ⟨inferInstance, by simp⟩ ⟨inferInstance, h'⟩⟩

Depends on / 依赖: existsUnique_of_le, unique
-/
lemma monoOfLE_eq_iff (h : x <= y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g] :
    monoOfLE h = g ↔ X.map g.op y.simplex = x.simplex :=
  ⟨by rintro rfl; simp,
    fun h' => (existsUnique_of_le h).unique ⟨inferInstance, by simp⟩ ⟨inferInstance, h'⟩⟩

variable (x) in
@[simp]
/--
lemma `monoOfLE_refl` / 引理 `monoOfLE_refl`

English:
lemma monoOfLE_refl
  statement: monoOfLE (le_refl x) = 𝟙 _
  proof: by
  simp [monoOfLE_eq_iff]

@[reassoc (attr := simp)]

中文:
引理 monoOfLE_refl
  结论: monoOfLE (le_refl x) = 𝟙 _
  证明: by
  simp [monoOfLE_eq_iff]

@[reassoc (attr := simp)]

Depends on / 依赖: monoOfLE_eq_iff
-/
lemma monoOfLE_refl : monoOfLE (le_refl x) = 𝟙 _ := by
  simp [monoOfLE_eq_iff]

@[reassoc (attr := simp)]
/--
lemma `monoOfLE_comp` / 引理 `monoOfLE_comp`

English:
lemma monoOfLE_comp
  given: (h' : y <= z)
  proof: by
  symm
  simp [monoOfLE_eq_iff]

中文:
引理 monoOfLE_comp
  条件: (h' : y <= z)
  证明: by
  symm
  simp [monoOfLE_eq_iff]

Depends on / 依赖: monoOfLE_eq_iff
-/
lemma monoOfLE_comp (h' : y <= z) :
    monoOfLE h ≫ monoOfLE h' = monoOfLE (h.trans h') := by
  symm
  simp [monoOfLE_eq_iff]

end N

end SSet
