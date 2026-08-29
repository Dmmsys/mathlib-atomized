/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Pullbacks in the category of types

In `Type*`, the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the
subtype `{ p : X × Y // f p.1 = g p.2 }` of the product.
We show some additional lemmas for pullbacks in the category of types.
-/

@[expose] public section

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} {X' Y' Z' : Type v}
variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')

/--
Definition of `PullbackObj` / `PullbackObj` 的定义

English:
abbreviation PullbackObj
  signature: : Type u
  body: { p : X × Y // f p.1 = g p.2 }

中文:
缩写 PullbackObj
  签名: : 类型u
  定义体: { p : X × Y // f p.1 = g p.2 }
-/
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }

-- `PullbackObj f g` comes with a coercion to the product type `X × Y`.
example (p : PullbackObj f g) : X × Y :=
  p

/--
Definition of `pullbackCone` / `pullbackCone` 的定义

English:
abbreviation pullbackCone
  signature: : Limits.PullbackCone f g
  body: PullbackCone.mk (↾fun p : PullbackObj f g => p.1.1)
    (↾fun p => p.1.2) (by ext p; exact p.2)

中文:
缩写 pullbackCone
  签名: : Limits.PullbackCone f g
  定义体: PullbackCone.mk (↾fun p : PullbackObj f g => p.1.1)
    (↾fun p => p.1.2) (by ext p; exact p.2)

Depends on / 依赖: PullbackCone, PullbackCone.mk, PullbackObj
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (↾fun p : PullbackObj f g => p.1.1)
    (↾fun p => p.1.2) (by ext p; exact p.2)

/-- The explicit pullback in the category of types, bundled up as a `LimitCone`
for given `f` and `g`.
-/
@[simps]
/--
Definition of `pullbackLimitCone` / `pullbackLimitCone` 的定义

English:
definition pullbackLimitCone
  signature: (f : X ⟶ Z) (g : Y ⟶ Z)
  body: pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s => ↾fun x => ⟨⟨s.fst x, s.snd x⟩, congr_hom s.condition x⟩)
      (by aesop) (by aesop) fun _ _ w =>
ConcreteCategory.ext TypeCat.Fun.ext funext fun x => Subtype.ext
        Prod.ext (congr_hom (w WalkingCospan.left) x) (congr_hom (w

中文:
定义 pullbackLimitCone
  签名: (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s => ↾fun x => ⟨⟨s.fst x, s.snd x⟩, congr_hom s.condition x⟩)
      (by aesop) (by aesop) fun _ _ w =>
ConcreteCategory.ext TypeCat.Fun.ext funext fun x => Subtype.ext
        Prod.ext (congr_hom (w WalkingCospan.left) x) (congr_hom (w

Depends on / 依赖: pullbackCone
-/
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  cone := pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s => ↾fun x => ⟨⟨s.fst x, s.snd x⟩, congr_hom s.condition x⟩)
      (by aesop) (by aesop) fun _ _ w =>
ConcreteCategory.ext TypeCat.Fun.ext funext fun x => Subtype.ext
        Prod.ext (congr_hom (w WalkingCospan.left) x) (congr_hom (w WalkingCospan.right) x)

end Types

namespace PullbackCone

variable {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : PullbackCone f g}

namespace IsLimit

variable (hc : IsLimit c)

/--
Definition of `equivPullbackObj` / `equivPullbackObj` 的定义

English:
definition equivPullbackObj
  signature: : c.pt ≃ Types.PullbackObj f g
  body: (IsLimit.conePointUniqueUpToIso hc (Types.pullbackLimitCone f g).isLimit).toEquiv

@[simp]

中文:
定义 equivPullbackObj
  签名: : c.pt ≃ Types.PullbackObj f g
  定义体: (IsLimit.conePointUniqueUpToIso hc (Types.pullbackLimitCone f g).isLimit).toEquiv

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, Types.pullbackLimitCone, conePointUniqueUpToIso, isLimit, pullbackLimitCone, toEquiv
-/
noncomputable def equivPullbackObj : c.pt ≃ Types.PullbackObj f g :=
  (IsLimit.conePointUniqueUpToIso hc (Types.pullbackLimitCone f g).isLimit).toEquiv

@[simp]
/--
lemma `equivPullbackObj_apply_fst` / 引理 `equivPullbackObj_apply_fst`

English:
lemma equivPullbackObj_apply_fst
  given: (x : c.pt)
  statement: (equivPullbackObj hc x).1.1 = c.fst x
  proof: (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .left)) x

@[simp]

中文:
引理 equivPullbackObj_apply_fst
  条件: (x : c.pt)
  结论: (equivPullbackObj hc x).1.1 = c.fst x
  证明: (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .left)) x

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, Types.pullbackLimitCone, conePointUniqueUpToIso_hom_comp, congr_hom, isLimit, pullbackLimitCone
-/
lemma equivPullbackObj_apply_fst (x : c.pt) : (equivPullbackObj hc x).1.1 = c.fst x :=
  (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .left)) x

@[simp]
/--
lemma `equivPullbackObj_apply_snd` / 引理 `equivPullbackObj_apply_snd`

English:
lemma equivPullbackObj_apply_snd
  given: (x : c.pt)
  statement: (equivPullbackObj hc x).1.2 = c.snd x
  proof: (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .right)) x

@[simp]

中文:
引理 equivPullbackObj_apply_snd
  条件: (x : c.pt)
  结论: (equivPullbackObj hc x).1.2 = c.snd x
  证明: (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .right)) x

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, Types.pullbackLimitCone, conePointUniqueUpToIso_hom_comp, congr_hom, isLimit, pullbackLimitCone
-/
lemma equivPullbackObj_apply_snd (x : c.pt) : (equivPullbackObj hc x).1.2 = c.snd x :=
  (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .right)) x

@[simp]
/--
lemma `equivPullbackObj_symm_apply_fst` / 引理 `equivPullbackObj_symm_apply_fst`

English:
lemma equivPullbackObj_symm_apply_fst
  given: (x : Types.PullbackObj f g)
  proof: by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

@[simp]

中文:
引理 equivPullbackObj_symm_apply_fst
  条件: (x : Types.PullbackObj f g)
  证明: by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

@[simp]

Depends on / 依赖: equivPullbackObj, surjective
-/
lemma equivPullbackObj_symm_apply_fst (x : Types.PullbackObj f g) :
    c.fst ((equivPullbackObj hc).symm x) = x.1.1 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

@[simp]
/--
lemma `equivPullbackObj_symm_apply_snd` / 引理 `equivPullbackObj_symm_apply_snd`

English:
lemma equivPullbackObj_symm_apply_snd
  given: (x : Types.PullbackObj f g)
  proof: by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

include hc in

中文:
引理 equivPullbackObj_symm_apply_snd
  条件: (x : Types.PullbackObj f g)
  证明: by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

include hc in

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, False.elim, Nonempty, Nonempty.some, Set.range, choose_spec, classical, equivPullbackObj, mono_iff_injective, rename_i, split_ifs, surjective
-/
lemma equivPullbackObj_symm_apply_snd (x : Types.PullbackObj f g) :
    c.snd ((equivPullbackObj hc).symm x) = x.1.2 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

include hc in
/--
lemma `type_ext` / 引理 `type_ext`

English:
lemma type_ext
  given: {x y : c.pt} (h₁ : c.fst x = c.fst y) (h₂ : c.snd x = c.snd y)
  statement: x = y
  proof: (equivPullbackObj hc).injective (by ext <;> assumption)

中文:
引理 type_ext
  条件: {x y : c.pt} (h₁ : c.fst x = c.fst y) (h₂ : c.snd x = c.snd y)
  结论: x = y
  证明: (equivPullbackObj hc).injective (by ext <;> assumption)

Depends on / 依赖: equivPullbackObj, injective
-/
lemma type_ext {x y : c.pt} (h₁ : c.fst x = c.fst y) (h₂ : c.snd x = c.snd y) : x = y :=
  (equivPullbackObj hc).injective (by ext <;> assumption)

end IsLimit

variable (c)

/-- Given `c : PullbackCone f g` in the category of types, this is
the canonical map `c.pt → Types.PullbackObj f g`. -/
@[simps coe_fst coe_snd]
/--
Definition of `toPullbackObj` / `toPullbackObj` 的定义

English:
definition toPullbackObj
  signature: (x : c.pt)
  body: ⟨⟨c.fst x, c.snd x⟩, congr_hom c.condition x⟩

中文:
定义 toPullbackObj
  签名: (x : c.pt)
  定义体: ⟨⟨c.fst x, c.snd x⟩, congr_hom c.condition x⟩

Depends on / 依赖: Limits, Limits.prod.fst, Limits.prod.lift, Limits.prod.snd, c.condition, c.fst, c.snd, comp_factorThru, comp_lift, condition, congr_hom, factorThru, lift_fst, lift_snd, prod.comp_lift, prod.lift_fst, prod.lift_snd
-/
def toPullbackObj (x : c.pt) : Types.PullbackObj f g :=
  ⟨⟨c.fst x, c.snd x⟩, congr_hom c.condition x⟩

/--
Definition of `isLimitEquivBijective` / `isLimitEquivBijective` 的定义

English:
definition isLimitEquivBijective
  signature: :
  body: (IsLimit.equivPullbackObj h).bijective
  invFun h := IsLimit.ofIsoLimit (Types.pullbackLimitCone f g).isLimit
    (Iso.symm (PullbackCone.ext (Equiv.ofBijective _ h).toIso))
  left_inv _ := Subsingleton.elim _ _

中文:
定义 isLimitEquivBijective
  签名: :
  定义体: (IsLimit.equivPullbackObj h).bijective
  invFun h := IsLimit.ofIsoLimit (Types.pullbackLimitCone f g).isLimit
    (Iso.symm (PullbackCone.ext (Equiv.ofBijective _ h).toIso))
  left_inv _ := Subsingleton.elim _ _

Depends on / 依赖: Category, Category.assoc, Fan.mk_, IsLimit, IsLimit.equivPullbackObj, Pi.lift, bijective, comp_factorThru, equivPullbackObj, factorThru, limit.lift_
-/
noncomputable def isLimitEquivBijective :
    IsLimit c ≃ Function.Bijective c.toPullbackObj where
  toFun h := (IsLimit.equivPullbackObj h).bijective
  invFun h := IsLimit.ofIsoLimit (Types.pullbackLimitCone f g).isLimit
    (Iso.symm (PullbackCone.ext (Equiv.ofBijective _ h).toIso))
  left_inv _ := Subsingleton.elim _ _

end PullbackCone

namespace Types

section Pullback

open CategoryTheory.Limits.WalkingCospan

variable {W X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)

/--
Definition of `pullbackIsoPullback` / `pullbackIsoPullback` 的定义

English:
definition pullbackIsoPullback
  signature: : pullback f g ≅ PullbackObj f g
  body: (PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback f g)).toIso

@[simp]

中文:
定义 pullbackIsoPullback
  签名: : pullback f g ≅ PullbackObj f g
  定义体: (PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback f g)).toIso

@[simp]

Depends on / 依赖: Category, Category.assoc, IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj, biprod, biprod.fst, biprod.lift, biprod.lift_fst, biprod.lift_snd, biprod.snd, comp_factorThru, equivPullbackObj, factorThru, lift_fst, lift_snd, pullbackIsPullback
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback f g)).toIso

@[simp]
/--
theorem `pullbackIsoPullback_hom_fst` / 定理 `pullbackIsoPullback_hom_fst`

English:
theorem pullbackIsoPullback_hom_fst
  given: (p : pullback f g)
  proof: PullbackCone.IsLimit.equivPullbackObj_apply_fst (pullbackIsPullback f g) p

@[simp]

中文:
定理 pullbackIsoPullback_hom_fst
  条件: (p : pullback f g)
  证明: PullbackCone.IsLimit.equivPullbackObj_apply_fst (pullbackIsPullback f g) p

@[simp]

Depends on / 依赖: Category, Category.assoc, IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj_apply_fst, biproduct, biproduct.lift, biproduct.lift_, comp_factorThru, equivPullbackObj_apply_fst, factorThru, pullbackIsPullback
-/
theorem pullbackIsoPullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).fst = (pullback.fst f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst (pullbackIsPullback f g) p

@[simp]
/--
theorem `pullbackIsoPullback_hom_snd` / 定理 `pullbackIsoPullback_hom_snd`

English:
theorem pullbackIsoPullback_hom_snd
  given: (p : pullback f g)
  proof: PullbackCone.IsLimit.equivPullbackObj_apply_snd (pullbackIsPullback f g) p

@[elementwise (attr := simp)]

中文:
定理 pullbackIsoPullback_hom_snd
  条件: (p : pullback f g)
  证明: PullbackCone.IsLimit.equivPullbackObj_apply_snd (pullbackIsPullback f g) p

@[elementwise (attr := simp)]

Depends on / 依赖: IsLimit, Projective, Projective.factorThru, PullbackCone, PullbackCone.IsLimit.equivPullbackObj_apply_snd, Quiver, Quiver.Hom.op_inj, equivPullbackObj_apply_snd, f.op, factorThru, g.op, op_inj, pullbackIsPullback
-/
theorem pullbackIsoPullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).snd = (pullback.snd f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd (pullbackIsPullback f g) p

@[elementwise (attr := simp)]
/--
theorem `pullbackIsoPullback_inv_fst` / 定理 `pullbackIsoPullback_inv_fst`

English:
theorem pullbackIsoPullback_inv_fst
  proof: by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackIsPullback f g) _

@[elementwise (attr := simp)]

中文:
定理 pullbackIsoPullback_inv_fst
  证明: by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackIsPullback f g) _

@[elementwise (attr := simp)]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst, Quiver, Quiver.Hom.op_inj, e.op, equivPullbackObj_symm_apply_fst, f.op, factorThru, op_inj, pullbackIsPullback
-/
theorem pullbackIsoPullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst _ _ =
      ↾fun p => (p.1 : X × Y).fst := by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackIsPullback f g) _

@[elementwise (attr := simp)]
/--
theorem `pullbackIsoPullback_inv_snd` / 定理 `pullbackIsoPullback_inv_snd`

English:
theorem pullbackIsoPullback_inv_snd
  proof: by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackIsPullback f g) _

中文:
定理 pullbackIsoPullback_inv_snd
  证明: by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackIsPullback f g) _

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd, Quiver, Quiver.Hom.unop_inj, e.unop, equivPullbackObj_symm_apply_snd, f.unop, factorThru, pullbackIsPullback, unop_inj
-/
theorem pullbackIsoPullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd _ _ =
      ↾fun p => (p.1 : X × Y).snd := by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackIsPullback f g) _

end Pullback

end Types

end CategoryTheory.Limits


namespace CategoryTheory.Limits.Types

variable {P X Y Z : Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
lemma `range_fst_of_isPullback` / 引理 `range_fst_of_isPullback`

English:
lemma range_fst_of_isPullback
  given: (h : IsPullback fst snd f g)
  proof: by
  let e := h.isoPullback ≪≫ Types.pullbackIsoPullback f g
  have : fst = _root_.Prod.fst ∘ Subtype.val ∘ e.hom := by
    ext p
    suffices fst p = pullback.fst f g (h.isoPullback.hom p) by simpa
    rw [← comp_apply h.isoPullback.hom (pullback.fst f g)]; rw [IsPullback.isoPullback_hom_fst]
  rw 

中文:
引理 range_fst_of_isPullback
  条件: (h : IsPullback fst snd f g)
  证明: by
  let e := h.isoPullback ≪≫ Types.pullbackIsoPullback f g
  have : fst = _root_.Prod.fst ∘ Subtype.val ∘ e.hom := by
    ext p
    suffices fst p = pullback.fst f g (h.isoPullback.hom p) by simpa
    rw [← comp_apply h.isoPullback.hom (pullback.fst f g)]; rw [IsPullback.isoPullback_hom_fst]
  rw 

Depends on / 依赖: IsPullback, IsPullback.isoPullback_hom_fst, Projective, Projective.factorThru, Quiver, Quiver.Hom.unop_inj, Set.range_comp, Set.range_eq_univ.mpr, Subtype, Subtype.val, Types.pullbackIsoPullback, _root_, _root_.Prod.fst, comp_apply, e.hom, eq_comm, f.unop, factorThru, g.unop, h.isoPullback
-/
lemma range_fst_of_isPullback (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  let e := h.isoPullback ≪≫ Types.pullbackIsoPullback f g
  have : fst = _root_.Prod.fst ∘ Subtype.val ∘ e.hom := by
    ext p
    suffices fst p = pullback.fst f g (h.isoPullback.hom p) by simpa
    rw [← comp_apply h.isoPullback.hom (pullback.fst f g)]; rw [IsPullback.isoPullback_hom_fst]
  rw [this]; rw [Set.range_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr (surjective_of_epi e.hom)]
  ext
  simp [eq_comm]

/--
lemma `range_snd_of_isPullback` / 引理 `range_snd_of_isPullback`

English:
lemma range_snd_of_isPullback
  given: (h : IsPullback fst snd f g)
  proof: by
  rw [range_fst_of_isPullback (IsPullback.flip h)]

中文:
引理 range_snd_of_isPullback
  条件: (h : IsPullback fst snd f g)
  证明: by
  rw [range_fst_of_isPullback (IsPullback.flip h)]

Depends on / 依赖: IsPullback, IsPullback.flip, range_fst_of_isPullback
-/
lemma range_snd_of_isPullback (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  rw [range_fst_of_isPullback (IsPullback.flip h)]

variable (f g)

@[simp]
/--
lemma `range_pullbackFst` / 引理 `range_pullbackFst`

English:
lemma range_pullbackFst
  statement: Set.range (pullback.fst f g) = f ⁻¹' Set.range g
  proof: range_fst_of_isPullback (.of_hasPullback f g)

@[simp]

中文:
引理 range_pullbackFst
  结论: Set.range (pullback.fst f g) = f ⁻¹' Set.range g
  证明: range_fst_of_isPullback (.of_hasPullback f g)

@[simp]

Depends on / 依赖: of_hasPullback, range_fst_of_isPullback
-/
lemma range_pullbackFst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g :=
  range_fst_of_isPullback (.of_hasPullback f g)

@[simp]
/--
lemma `range_pullbackSnd` / 引理 `range_pullbackSnd`

English:
lemma range_pullbackSnd
  statement: Set.range (pullback.snd f g) = g ⁻¹' Set.range f
  proof: range_snd_of_isPullback (.of_hasPullback f g)

中文:
引理 range_pullbackSnd
  结论: Set.range (pullback.snd f g) = g ⁻¹' Set.range f
  证明: range_snd_of_isPullback (.of_hasPullback f g)

Depends on / 依赖: of_hasPullback, range_snd_of_isPullback
-/
lemma range_pullbackSnd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f :=
  range_snd_of_isPullback (.of_hasPullback f g)

section

variable {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄}
  {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `ext_of_isPullback` / 引理 `ext_of_isPullback`

English:
lemma ext_of_isPullback
  statement: (h : IsPullback t l r b) {x₁ y₁ : X₁}
  proof: (h.isLimit.conePointUniqueUpToIso (Types.pullbackLimitCone _ _).isLimit).toEquiv.injective
    (by dsimp; ext <;> assumption)

中文:
引理 ext_of_isPullback
  结论: (h : IsPullback t l r b) {x₁ y₁ : X₁}
  证明: (h.isLimit.conePointUniqueUpToIso (Types.pullbackLimitCone _ _).isLimit).toEquiv.injective
    (by dsimp; ext <;> assumption)

Depends on / 依赖: Types.pullbackLimitCone, conePointUniqueUpToIso, h.isLimit.conePointUniqueUpToIso, injective, isLimit, pullbackLimitCone, toEquiv, toEquiv.injective
-/
lemma ext_of_isPullback (h : IsPullback t l r b) {x₁ y₁ : X₁}
    (h₁ : t x₁ = t y₁) (h₂ : l x₁ = l y₁) : x₁ = y₁ :=
  (h.isLimit.conePointUniqueUpToIso (Types.pullbackLimitCone _ _).isLimit).toEquiv.injective
    (by dsimp; ext <;> assumption)

/--
lemma `exists_of_isPullback` / 引理 `exists_of_isPullback`

English:
lemma exists_of_isPullback
  statement: (h : IsPullback t l r b)
  proof: by
  obtain ⟨x₁, hx₁⟩ :=
    (PullbackCone.IsLimit.equivPullbackObj h.isLimit).surjective ⟨⟨x₂, x₃⟩, hx⟩
  rw [Subtype.ext_iff] at hx₁
  exact ⟨x₁, congr_arg _root_.Prod.fst hx₁,
    congr_arg _root_.Prod.snd hx₁⟩

中文:
引理 exists_of_isPullback
  结论: (h : IsPullback t l r b)
  证明: by
  obtain ⟨x₁, hx₁⟩ :=
    (PullbackCone.IsLimit.equivPullbackObj h.isLimit).surjective ⟨⟨x₂, x₃⟩, hx⟩
  rw [Subtype.ext_iff] at hx₁
  exact ⟨x₁, congr_arg _root_.Prod.fst hx₁,
    congr_arg _root_.Prod.snd hx₁⟩

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj, Subtype, Subtype.ext_iff, _root_, _root_.Prod.fst, _root_.Prod.snd, congr_arg, equivPullbackObj, ext_iff, h.isLimit, isLimit, surjective
-/
lemma exists_of_isPullback (h : IsPullback t l r b)
    (x₂ : X₂) (x₃ : X₃) (hx : r x₂ = b x₃) :
    exists x₁, t x₁ = x₂ ∧ l x₁ = x₃ := by
  obtain ⟨x₁, hx₁⟩ :=
    (PullbackCone.IsLimit.equivPullbackObj h.isLimit).surjective ⟨⟨x₂, x₃⟩, hx⟩
  rw [Subtype.ext_iff] at hx₁
  exact ⟨x₁, congr_arg _root_.Prod.fst hx₁,
    congr_arg _root_.Prod.snd hx₁⟩

set_option backward.isDefEq.respectTransparency false in
variable (t l r b) in
/--
lemma `isPullback_iff` / 引理 `isPullback_iff`

English:
lemma isPullback_iff
  proof: by
  constructor
  · intro h
    exact ⟨h.w, fun x₁ y₁ ⟨h₁, h₂⟩ => ext_of_isPullback h h₁ h₂, exists_of_isPullback h⟩
  · rintro ⟨w, h₁, h₂⟩
    let φ : X₁ ⟶ PullbackObj r b := ↾fun x₁ => ⟨⟨t x₁, l x₁⟩, congr_hom w x₁⟩
    have hφ : IsIso φ := by
      rw [isIso_iff_bijective]
      constructor
    

中文:
引理 isPullback_iff
  证明: by
  constructor
  · intro h
    exact ⟨h.w, fun x₁ y₁ ⟨h₁, h₂⟩ => ext_of_isPullback h h₁ h₂, exists_of_isPullback h⟩
  · rintro ⟨w, h₁, h₂⟩
    let φ : X₁ ⟶ PullbackObj r b := ↾fun x₁ => ⟨⟨t x₁, l x₁⟩, congr_hom w x₁⟩
    have hφ : IsIso φ := by
      rw [isIso_iff_bijective]
      constructor
    

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, PullbackCone, PullbackCone.ext, PullbackObj, Types.pullbackLimitCone, cat_disch, congr_hom, exists_of_isPullback, ext_of_isPullback, isIso_iff_bijective, isLimit, ofIsoLimit, pullbackLimitCone
-/
lemma isPullback_iff :
  IsPullback t l r b ↔ t ≫ r = l ≫ b ∧
    (forall x₁ y₁, t x₁ = t y₁ ∧ l x₁ = l y₁ -> x₁ = y₁) ∧
    forall x₂ x₃, r x₂ = b x₃ -> exists x₁, t x₁ = x₂ ∧ l x₁ = x₃ := by
  constructor
  · intro h
    exact ⟨h.w, fun x₁ y₁ ⟨h₁, h₂⟩ => ext_of_isPullback h h₁ h₂, exists_of_isPullback h⟩
  · rintro ⟨w, h₁, h₂⟩
    let φ : X₁ ⟶ PullbackObj r b := ↾fun x₁ => ⟨⟨t x₁, l x₁⟩, congr_hom w x₁⟩
    have hφ : IsIso φ := by
      rw [isIso_iff_bijective]
      constructor
      · intro _ _ h
        simp [φ] at h
        grind
      · intro x
        obtain ⟨a, ha⟩ := h₂ x.1.1 x.1.2 (by grind)
        cat_disch
    exact ⟨⟨w⟩, ⟨IsLimit.ofIsoLimit ((Types.pullbackLimitCone r b).isLimit)
      (PullbackCone.ext (asIso φ)).symm⟩⟩

end

end CategoryTheory.Limits.Types
