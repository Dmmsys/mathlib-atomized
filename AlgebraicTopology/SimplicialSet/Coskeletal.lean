/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial sets

In this file, we prove that if `X` is `StrictSegal` then `X` is 2-coskeletal,
i.e. `X ≅ (cosk 2).obj X`. In particular, nerves of categories are 2-coskeletal.

This isomorphism follows from the fact that `rightExtensionInclusion X 2` is a right Kan
extension. In fact, we show that when `X` is `StrictSegal` then
`(rightExtensionInclusion X n).IsPointwiseRightKanExtension` holds.

As an example, `SimplicialObject.IsCoskeletal (nerve C) 2` shows that nerves of categories are
2-coskeletal.
-/

@[expose] public section


universe v u

open CategoryTheory Simplicial SimplexCategory Truncated
open Opposite Category Functor Limits

namespace SSet

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op`. -/
@[simps! left right_as hom_app]
/--
Definition of `rightExtensionInclusion` / `rightExtensionInclusion` 的定义

English:
definition rightExtensionInclusion
  signature: (X : SSet.{u}) (n : Nat)
  body: RightExtension.mk _ (𝟙 _)

中文:
定义 rightExtensionInclusion
  签名: (X : SSet.{u}) (n : 自然数)
  定义体: RightExtension.mk _ (𝟙 _)
-/
def rightExtensionInclusion (X : SSet.{u}) (n : Nat) :
    RightExtension (Truncated.inclusion (n := n)).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

section

open StructuredArrow

namespace StrictSegal
variable {X : SSet.{u}} (sx : StrictSegal X)

namespace isPointwiseRightKanExtensionAt

/--
Definition of `strArrowMk₂` / `strArrowMk₂` 的定义

English:
abbreviation strArrowMk₂
  signature: {i : Nat} {n : Nat} (φ : ⦋i⦌ ⟶ ⦋n⦌) (hi : i <= 2 := by lia)
  body: StructuredArrow.mk (Y := op ⦋i⦌₂) φ.op

中文:
缩写 strArrowMk₂
  签名: {i : 自然数} {n : 自然数} (φ : ⦋i⦌ ⟶ ⦋n⦌) (hi : i <= 2 := by lia)
  定义体: StructuredArrow.mk (Y := op ⦋i⦌₂) φ.op

Depends on / 依赖: StructuredArrow, StructuredArrow.mk, Truncated, Truncated.inclusion, inclusion
-/
abbrev strArrowMk₂ {i : Nat} {n : Nat} (φ : ⦋i⦌ ⟶ ⦋n⦌) (hi : i <= 2 := by lia) :
    StructuredArrow (op ⦋n⦌) (Truncated.inclusion 2).op :=
  StructuredArrow.mk (Y := op ⦋i⦌₂) φ.op

/-- Given a term in the cone over the diagram
`(proj (op ⦋n⦌) ((Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X)` where `X` is
Strict Segal, one can produce an `n`-simplex in `X`. -/
@[simp]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {X : SSet.{u}} (sx : StrictSegal X) {n}
  body: sx.spineToSimplex {
    vertex := fun i => s.π.app (.mk (Y := op ⦋0⦌₂) (.op (SimplexCategory.const _ _ i))) x
    arrow := fun i => s.π.app (.mk (Y := op ⦋1⦌₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i)))) x
    arrow_src := fun i => by
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) 

中文:
定义 lift
  签名: {X : SSet.{u}} (sx : StrictSegal X) {n}
  定义体: sx.spineToSimplex {
    vertex := fun i => s.π.app (.mk (Y := op ⦋0⦌₂) (.op (SimplexCategory.const _ _ i))) x
    arrow := fun i => s.π.app (.mk (Y := op ⦋1⦌₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i)))) x
    arrow_src := fun i => by
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Fin.castSucc_le_succ, Hom.tr, Quiver, Quiver.Hom.unop_inj, SimplexCategory, SimplexCategory.const, StructuredArrow, StructuredArrow.homMk, arrow_src, arrow_tgt, castSucc, castSucc_le_succ, congr_hom, fin_cases, i.castSucc, mkOfLe, spineToSimplex, sx.spineToSimplex
-/
noncomputable def lift {X : SSet.{u}} (sx : StrictSegal X) {n}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙
      (Truncated.inclusion 2).op ⋙ X)) (x : s.pt) : X _⦋n⦌ :=
  sx.spineToSimplex {
    vertex := fun i => s.π.app (.mk (Y := op ⦋0⦌₂) (.op (SimplexCategory.const _ _ i))) x
    arrow := fun i => s.π.app (.mk (Y := op ⦋1⦌₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i)))) x
    arrow_src := fun i => by
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) ⟶
        strArrowMk₂ (⦋0⦌.const _ i.castSucc) :=
          StructuredArrow.homMk (Hom.tr (δ 1)).op
          (Quiver.Hom.unop_inj (by ext x; fin_cases x; rfl))
      exact ConcreteCategory.congr_hom (s.w φ) x
    arrow_tgt := fun i => by
      dsimp
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) ⟶
          strArrowMk₂ (⦋0⦌.const _ i.succ) :=
        StructuredArrow.homMk (Hom.tr (δ 0)).op
          (Quiver.Hom.unop_inj (by ext x; fin_cases x; rfl))
      exact ConcreteCategory.congr_hom (s.w φ) x }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `fac_aux₁` / 引理 `fac_aux₁`

English:
lemma fac_aux₁
  statement: {n : Nat}
  proof: by
  dsimp [lift]
  rw [spineToSimplex_arrow]
  rfl

中文:
引理 fac_aux₁
  结论: {n : 自然数}
  证明: by
  dsimp [lift]
  rw [spineToSimplex_arrow]
  rfl

Depends on / 依赖: spineToSimplex_arrow
-/
lemma fac_aux₁ {n : Nat}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (i : Nat) (hi : i < n) :
    X.map (mkOfSucc ⟨i, hi⟩).op (lift sx s x) =
      s.π.app (strArrowMk₂ (mkOfSucc ⟨i, hi⟩)) x := by
  dsimp [lift]
  rw [spineToSimplex_arrow]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `fac_aux₂` / 引理 `fac_aux₂`

English:
lemma fac_aux₂
  statement: {n : Nat}
  proof: by
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  revert i j
  induction k with
  | zero =>
      rintro i j hij hj hik
      obtain rfl : i = j := hik
      have : mkOfLe ⟨i, Nat.lt_add_one_of_le hj⟩ ⟨i, Nat.lt_add_one_of_le hj⟩ (by rfl) =
        ⦋1⦌.const ⦋0⦌ 0 ≫ ⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩

中文:
引理 fac_aux₂
  结论: {n : 自然数}
  证明: by
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  revert i j
  induction k with
  | zero =>
      rintro i j hij hj hik
      obtain rfl : i = j := hik
      have : mkOfLe ⟨i, Nat.lt_add_one_of_le hj⟩ ⟨i, Nat.lt_add_one_of_le hj⟩ (by rfl) =
        ⦋1⦌.const ⦋0⦌ 0 ≫ ⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩

Depends on / 依赖: Hom.ext_one_left, Hom.tr, Nat.le.dest, Nat.lt_add_one_of_le, StructuredArrow, StructuredArrow.homMk, ext_one_left, lt_add_one_of_le, mkOfLe, revert
-/
lemma fac_aux₂ {n : Nat}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (i j : Nat) (hij : i <= j) (hj : j <= n) :
    X.map (mkOfLe ⟨i, by lia⟩ ⟨j, by lia⟩ hij).op (lift sx s x) =
      s.π.app (strArrowMk₂ (mkOfLe ⟨i, by lia⟩ ⟨j, by lia⟩ hij)) x := by
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  revert i j
  induction k with
  | zero =>
      rintro i j hij hj hik
      obtain rfl : i = j := hik
      have : mkOfLe ⟨i, Nat.lt_add_one_of_le hj⟩ ⟨i, Nat.lt_add_one_of_le hj⟩ (by rfl) =
        ⦋1⦌.const ⦋0⦌ 0 ≫ ⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩ := Hom.ext_one_left _ _
      rw [this]
      let α : (strArrowMk₂ (⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩)) ⟶
        (strArrowMk₂ (⦋1⦌.const ⦋0⦌ 0 ≫ ⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩)) :=
            StructuredArrow.homMk ((Hom.tr (⦋1⦌.const ⦋0⦌ 0)).op) (by simp; rfl)
      conv_rhs => dsimp; rw [dsimp% s.π.naturality_apply α x]
      rw [op_comp]; rw [Functor.map_comp]
      simp only [types_comp_apply]
      refine congrArg (X.map (⦋1⦌.const ⦋0⦌ 0).op) ?_
      unfold strArrowMk₂
      rw [lift]; rw [StrictSegal.spineToSimplex_vertex]
      congr
  | succ k hk =>
      intro i j hij hj hik
      let α := strArrowMk₂ (mkOfLeComp (n := n) ⟨i, by omega⟩ ⟨i + k, by omega⟩
          ⟨j, by omega⟩ (by simp) (by simp only [Fin.mk_le_mk]; omega))
      let α₀ := strArrowMk₂ (mkOfLe (n := n) ⟨i + k, by omega⟩ ⟨j, by omega⟩
        (by simp only [Fin.mk_le_mk]; omega))
      let α₁ := strArrowMk₂ (mkOfLe (n := n) ⟨i, by omega⟩ ⟨j, by omega⟩ hij)
      let α₂ := strArrowMk₂ (mkOfLe (n := n) ⟨i, by omega⟩ ⟨i + k, by omega⟩ (by simp))
      let β₀ : α ⟶ α₀ := StructuredArrow.homMk ((Hom.tr (mkOfSucc 1)).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      let β₁ : α ⟶ α₁ := StructuredArrow.homMk ((Hom.tr (δ 1)).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      let β₂ : α ⟶ α₂ := StructuredArrow.homMk ((Hom.tr (mkOfSucc 0)).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      have h₀ : X.map α₀.hom (lift sx s x) = s.π.app α₀ x := by
        subst hik
        exact fac_aux₁ _ _ _ _ hj
      have h₂ : X.map α₂.hom (lift sx s x) = s.π.app α₂ x :=
        hk i (i + k) (by simp) (by lia) rfl
      change X.map α₁.hom (lift sx s x) = s.π.app α₁ x
      have : X.map α.hom (lift sx s x) = s.π.app α x := by
        apply sx.spineInjective
        apply Path.ext'
        intro t
        dsimp [spineEquiv, α]
        rw [← Functor.map_comp_apply]
        match t with
        | 0 =>
            have : α.hom ≫ (mkOfSucc 0).op = α₂.hom :=
              Quiver.Hom.unop_inj (by ext x; fin_cases x <;> rfl)
            rw [dsimp% [α] this]
            dsimp [α₂] at h₂ ⊢
            rw [h₂]; rw [← dsimp% [α₂] ConcreteCategory.congr_hom (s.w β₂) x]
            rfl
        | 1 =>
            have : α.hom ≫ (mkOfSucc 1).op = α₀.hom :=
              Quiver.Hom.unop_inj (by ext x; fin_cases x <;> rfl)
            rw [dsimp% [α] this]
            dsimp [α₀] at h₀ ⊢
            rw [h₀]; rw [← dsimp% [α₀] ConcreteCategory.congr_hom (s.w β₀) x]
            rfl
      rw [← StructuredArrow.w β₁]; rw [Functor.map_comp_apply]
      dsimp [fromPUnit] at this ⊢
      rw [this]; rw [← s.w β₁]
      dsimp

/--
lemma `fac_aux₃` / 引理 `fac_aux₃`

English:
lemma fac_aux₃
  statement: {n : Nat}
  proof: by
  obtain ⟨i, j, hij, rfl⟩ : exists i j hij, φ = mkOfLe i j hij :=
    ⟨φ.toOrderHom 0, φ.toOrderHom 1, φ.toOrderHom.monotone (by decide),
      Hom.ext_one_left _ _ rfl rfl⟩
  exact fac_aux₂ _ _ _ _ _ _ (by lia)

中文:
引理 fac_aux₃
  结论: {n : 自然数}
  证明: by
  obtain ⟨i, j, hij, rfl⟩ : exists i j hij, φ = mkOfLe i j hij :=
    ⟨φ.toOrderHom 0, φ.toOrderHom 1, φ.toOrderHom.monotone (by decide),
      Hom.ext_one_left _ _ rfl rfl⟩
  exact fac_aux₂ _ _ _ _ _ _ (by lia)

Depends on / 依赖: Hom.ext_one_left, ext_one_left, mkOfLe, monotone, toOrderHom, toOrderHom.monotone
-/
lemma fac_aux₃ {n : Nat}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (φ : ⦋1⦌ ⟶ ⦋n⦌) :
    X.map φ.op (lift sx s x) = s.π.app (strArrowMk₂ φ) x := by
  obtain ⟨i, j, hij, rfl⟩ : exists i j hij, φ = mkOfLe i j hij :=
    ⟨φ.toOrderHom 0, φ.toOrderHom 1, φ.toOrderHom.monotone (by decide),
      Hom.ext_one_left _ _ rfl rfl⟩
  exact fac_aux₂ _ _ _ _ _ _ (by lia)

end isPointwiseRightKanExtensionAt

open Truncated

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open isPointwiseRightKanExtensionAt in
/--
Definition of `isPointwiseRightKanExtensionAt` / `isPointwiseRightKanExtensionAt` 的定义

English:
definition isPointwiseRightKanExtensionAt
  signature: (n : Nat)
  body: ↾fun x => lift sx s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : exists j, ⦋j⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    apply sx.spineInjective
    ext k
    · dsimp only [spineEquiv, Equiv.coe_fn_mk]
      rw [dsimp% show op f = f.op 

中文:
定义 isPointwiseRightKanExtensionAt
  签名: (n : 自然数)
  定义体: ↾fun x => lift sx s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : exists j, ⦋j⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    apply sx.spineInjective
    ext k
    · dsimp only [spineEquiv, Equiv.coe_fn_mk]
      rw [dsimp% show op f = f.op 
-/
noncomputable def isPointwiseRightKanExtensionAt (n : Nat) :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtensionAt ⟨⦋n⦌⟩ where
  lift s := ↾fun x => lift sx s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : exists j, ⦋j⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    apply sx.spineInjective
    ext k
    · dsimp only [spineEquiv, Equiv.coe_fn_mk]
      rw [dsimp% show op f = f.op from rfl]
      rw [spine_map_vertex]; rw [spine_spineToSimplex_apply]; rw [spine_vertex]
      let α : strArrowMk₂ f hi ⟶ strArrowMk₂ (⦋0⦌.const ⦋n⦌ (f.toOrderHom k)) :=
        StructuredArrow.homMk ((Hom.tr (⦋0⦌.const _ (by exact k))).op) (by simp; rfl)
      exact ConcreteCategory.congr_hom (s.w α).symm x
    · dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
      rw [← Functor.map_comp_apply]
      let α : strArrowMk₂ f ⟶ strArrowMk₂ (mkOfSucc k ≫ f) :=
        StructuredArrow.homMk (Hom.tr (mkOfSucc k)).op (by simp)
      exact (isPointwiseRightKanExtensionAt.fac_aux₃ _ _ _ _).trans
        (ConcreteCategory.congr_hom (s.w α).symm x)
  uniq s m hm := by
    ext x
    apply sx.spineInjective (X := X)
    -- simp? [spineEquiv] says:
    simp only [spineEquiv, RightExtension.coneAt_pt, rightExtensionInclusion_left,
      TypeCat.Fun.toFun_apply, Equiv.coe_fn_mk, lift, Nat.reduceAdd, ObjectProperty.ι_obj,
      const_obj_obj, comp_obj, proj_obj, mk_right, op_obj, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      spine_spineToSimplex_apply]
    ext i
    · exact ConcreteCategory.congr_hom (hm (StructuredArrow.mk
        (Y := op ⦋0⦌₂) (⦋0⦌.const ⦋n⦌ i).op)) x
    · exact ConcreteCategory.congr_hom (hm (.mk (Y := op ⦋1⦌₂)
        (.op (mkOfLe _ _ (Fin.castSucc_le_succ i))))) x

/--
Definition of `isPointwiseRightKanExtension` / `isPointwiseRightKanExtension` 的定义

English:
definition isPointwiseRightKanExtension
  signature: :
  body: fun Δ => sx.isPointwiseRightKanExtensionAt Δ.unop.len

中文:
定义 isPointwiseRightKanExtension
  签名: :
  定义体: fun Δ => sx.isPointwiseRightKanExtensionAt Δ.unop.len

Depends on / 依赖: isPointwiseRightKanExtensionAt, sx.isPointwiseRightKanExtensionAt, unop.len
-/
noncomputable def isPointwiseRightKanExtension :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtension :=
  fun Δ => sx.isPointwiseRightKanExtensionAt Δ.unop.len

/--
theorem `isRightKanExtension` / 定理 `isRightKanExtension`

English:
theorem isRightKanExtension
  given: (sx : StrictSegal X)
  proof: RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    sx.isPointwiseRightKanExtension

中文:
定理 isRightKanExtension
  条件: (sx : StrictSegal X)
  证明: RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    sx.isPointwiseRightKanExtension

Depends on / 依赖: IsPointwiseRightKanExtension, RightExtension, RightExtension.IsPointwiseRightKanExtension.isRightKanExtension, isPointwiseRightKanExtension, isRightKanExtension, sx.isPointwiseRightKanExtension
-/
theorem isRightKanExtension (sx : StrictSegal X) :
    X.IsRightKanExtension (𝟙 ((inclusion 2).op ⋙ X)) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    sx.isPointwiseRightKanExtension

/--
theorem `isCoskeletal` / 定理 `isCoskeletal`

English:
theorem isCoskeletal
  given: (sx : StrictSegal X)
  proof: sx.isRightKanExtension

中文:
定理 isCoskeletal
  条件: (sx : StrictSegal X)
  证明: sx.isRightKanExtension

Depends on / 依赖: isRightKanExtension, sx.isRightKanExtension
-/
theorem isCoskeletal (sx : StrictSegal X) :
    SimplicialObject.IsCoskeletal X 2 where
  isRightKanExtension := sx.isRightKanExtension

/--
Instance `isCoskeletal'` / 实例 `isCoskeletal'`

English:
instance isCoskeletal'
  signature: [IsStrictSegal X]
  body: isCoskeletal ofIsStrictSegal X

中文:
实例 isCoskeletal'
  签名: [是StrictSegal X]
  定义体: isCoskeletal ofIsStrictSegal X

Depends on / 依赖: isCoskeletal, ofIsStrictSegal
-/
instance isCoskeletal' [IsStrictSegal X] : SimplicialObject.IsCoskeletal X 2 :=
isCoskeletal ofIsStrictSegal X

end StrictSegal

end

end SSet

namespace CategoryTheory

namespace Nerve

open SSet

instance (C : Type u) [Category.{v} C] :
    SimplicialObject.IsCoskeletal (nerve C) 2 := inferInstance

/--
Definition of `nerveFunctor₂` / `nerveFunctor₂` 的定义

English:
definition nerveFunctor₂
  signature: : Cat.{v, u} ⥤ SSet.Truncated 2
  body: nerveFunctor ⋙ truncation 2

中文:
定义 nerveFunctor₂
  签名: : Cat.{v, u} ⥤ SSet.Truncated 2
  定义体: nerveFunctor ⋙ truncation 2

Depends on / 依赖: nerveFunctor, truncation
-/
def nerveFunctor₂ : Cat.{v, u} ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

set_option backward.defeqAttrib.useBackward true in
instance (X : Cat.{v, u}) : (nerveFunctor₂.obj X).IsStrictSegal := by
  dsimp [nerveFunctor₂]
  infer_instance

/--
Definition of `cosk₂Iso` / `cosk₂Iso` 的定义

English:
definition cosk₂Iso
  signature: : nerveFunctor.{v, u} ≅ nerveFunctor₂.{v, u} ⋙ Truncated.cosk 2
  body: NatIso.ofComponents (fun C => (nerve C).isoCoskOfIsCoskeletal 2)
    (fun _ => (coskAdj 2).unit.naturality _)

中文:
定义 cosk₂Iso
  签名: : nerveFunctor.{v, u} ≅ nerveFunctor₂.{v, u} ⋙ Truncated.cosk 2
  定义体: NatIso.ofComponents (fun C => (nerve C).isoCoskOfIsCoskeletal 2)
    (fun _ => (coskAdj 2).unit.naturality _)

Depends on / 依赖: NatIso, NatIso.ofComponents, coskAdj, isoCoskOfIsCoskeletal, naturality, ofComponents, unit.naturality
-/
noncomputable def cosk₂Iso : nerveFunctor.{v, u} ≅ nerveFunctor₂.{v, u} ⋙ Truncated.cosk 2 :=
  NatIso.ofComponents (fun C => (nerve C).isoCoskOfIsCoskeletal 2)
    (fun _ => (coskAdj 2).unit.naturality _)

end Nerve

end CategoryTheory
