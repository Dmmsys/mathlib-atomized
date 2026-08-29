/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Constructors for combining (co)fans

We provide constructors for combining (co)fans and show their (co)limit properties.

## TODO

* Combine (co)fans on sigma types

-/

@[expose] public section

universe u₁ u₂

namespace CategoryTheory

namespace Limits

variable {C : Type u₁} [Category.{u₂} C]

namespace Fan

variable {ι₁ ι₂ : Type*} {X : C} {f₁ : ι₁ -> C} {f₂ : ι₂ -> C}
    (c₁ : Fan f₁) (c₂ : Fan f₂) (bc : BinaryFan c₁.pt c₂.pt)
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (h : IsLimit bc)

/-- For fans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary fan on their
cone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂` -/
@[simp]
/--
Definition of `combPairHoms` / `combPairHoms` 的定义

English:
abbreviation combPairHoms
  signature: : (i : ι₁ oplus ι₂) -> bc.pt ⟶ Sum.elim f₁ f₂ i

中文:
缩写 combPairHoms
  签名: : (i : ι₁ oplus ι₂) -> bc.pt ⟶ 和.elim f₁ f₂ i
-/
abbrev combPairHoms : (i : ι₁ oplus ι₂) -> bc.pt ⟶ Sum.elim f₁ f₂ i
  | .inl a => bc.fst ≫ c₁.proj a
  | .inr a => bc.snd ≫ c₂.proj a

variable {c₁ c₂ bc}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `combPairIsLimit` / `combPairIsLimit` 的定义

English:
definition combPairIsLimit
  signature: : IsLimit (Fan.mk bc.pt (combPairHoms c₁ c₂ bc))
  body: Fan.IsLimit.mk _
    (fun s => Fan.IsLimit.lift h <| fun i => by
      cases i
      · exact Fan.IsLimit.lift h₁ (fun a => s.proj (.inl a))
      · exact Fan.IsLimit.lift h₂ (fun a => s.proj (.inr a)))
    (fun s w => by
      cases w <;>
      · simp only [fan_mk_proj, combPairHoms]
        erw [← Category.assoc, h.fac]
        simp only [pair_obj_left, mk_π_app, IsLimit.fac])
    (fun s m hm => Fan.IsLimit.hom_ext h _ _ <| fun w => by
      cases w
      · refine Fan.IsLimit.hom_ext h₁ _ _ (fun a => by aesop)
      · refine Fan.IsLimit.hom_ext h₂ _ _ (fun a => by aesop))

中文:
定义 combPairIsLimit
  签名: : 是极限 (Fan.mk bc.pt (combPairHoms c₁ c₂ bc))
  定义体: Fan.IsLimit.mk _
    (fun s => Fan.IsLimit.lift h <| fun i => by
      cases i
      · exact Fan.IsLimit.lift h₁ (fun a => s.proj (.inl a))
      · exact Fan.IsLimit.lift h₂ (fun a => s.proj (.inr a)))
    (fun s w => by
      cases w <;>
      · simp only [fan_mk_proj, combPairHoms]
        erw [← Category.assoc, h.fac]
        simp only [pair_obj_left, mk_π_app, IsLimit.fac])
    (fun s m hm => Fan.IsLimit.hom_ext h _ _ <| fun w => by
      cases w
      · refine Fan.IsLimit.hom_ext h₁ _ _ (fun a => by aesop)
      · refine Fan.IsLimit.hom_ext h₂ _ _ (fun a => by aesop))

Depends on / 依赖: Category, Category.assoc, Fan.IsLimit.hom_ext, Fan.IsLimit.lift, Fan.IsLimit.mk, IsLimit, IsLimit.fac, combPairHoms, fan_mk_proj, h.fac, hom_ext, pair_obj_left, s.proj
-/
def combPairIsLimit : IsLimit (Fan.mk bc.pt (combPairHoms c₁ c₂ bc)) :=
  Fan.IsLimit.mk _
    (fun s => Fan.IsLimit.lift h <| fun i => by
      cases i
      · exact Fan.IsLimit.lift h₁ (fun a => s.proj (.inl a))
      · exact Fan.IsLimit.lift h₂ (fun a => s.proj (.inr a)))
    (fun s w => by
      cases w <;>
      · simp only [fan_mk_proj, combPairHoms]
        erw [← Category.assoc, h.fac]
        simp only [pair_obj_left, mk_π_app, IsLimit.fac])
    (fun s m hm => Fan.IsLimit.hom_ext h _ _ <| fun w => by
      cases w
      · refine Fan.IsLimit.hom_ext h₁ _ _ (fun a => by aesop)
      · refine Fan.IsLimit.hom_ext h₂ _ _ (fun a => by aesop))

end Fan

namespace Cofan

variable {ι₁ ι₂ : Type*} {X : C} {f₁ : ι₁ -> C} {f₂ : ι₂ -> C}
    (c₁ : Cofan f₁) (c₂ : Cofan f₂) (bc : BinaryCofan c₁.pt c₂.pt)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (h : IsColimit bc)

/-- For cofans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary cofan on their
cocone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂` -/
@[simp]
/--
Definition of `combPairHoms` / `combPairHoms` 的定义

English:
abbreviation combPairHoms
  signature: : (i : ι₁ oplus ι₂) -> Sum.elim f₁ f₂ i ⟶ bc.pt

中文:
缩写 combPairHoms
  签名: : (i : ι₁ oplus ι₂) -> 和.elim f₁ f₂ i ⟶ bc.pt
-/
abbrev combPairHoms : (i : ι₁ oplus ι₂) -> Sum.elim f₁ f₂ i ⟶ bc.pt
  | .inl a => c₁.inj a ≫ bc.inl
  | .inr a => c₂.inj a ≫ bc.inr

variable {c₁ c₂ bc}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `combPairIsColimit` / `combPairIsColimit` 的定义

English:
definition combPairIsColimit
  signature: : IsColimit (Cofan.mk bc.pt (combPairHoms c₁ c₂ bc))
  body: Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc h <| fun i => by
      cases i
      · exact Cofan.IsColimit.desc h₁ (fun a => s.inj (.inl a))
      · exact Cofan.IsColimit.desc h₂ (fun a => s.inj (.inr a)))
    (fun s w => by
      cases w <;>
      · simp only [cofan_mk_inj, combPairHoms, Category.assoc]
        erw [h.fac]
        simp only [Cofan.mk_ι_app, Cofan.IsColimit.fac])
    (fun s m hm => Cofan.IsColimit.hom_ext h _ _ <| fun w => by
      cases w
      · refine Cofan.IsColimit.hom_ext h₁ _ _ (fun a => by aesop)
      · refine Cofan.IsColimit.hom_ext h₂ _ _ (fun a => by aesop))

中文:
定义 combPairIsColimit
  签名: : 是余极限 (Cofan.mk bc.pt (combPairHoms c₁ c₂ bc))
  定义体: Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc h <| fun i => by
      cases i
      · exact Cofan.IsColimit.desc h₁ (fun a => s.inj (.inl a))
      · exact Cofan.IsColimit.desc h₂ (fun a => s.inj (.inr a)))
    (fun s w => by
      cases w <;>
      · simp only [cofan_mk_inj, combPairHoms, Category.assoc]
        erw [h.fac]
        simp only [Cofan.mk_ι_app, Cofan.IsColimit.fac])
    (fun s m hm => Cofan.IsColimit.hom_ext h _ _ <| fun w => by
      cases w
      · refine Cofan.IsColimit.hom_ext h₁ _ _ (fun a => by aesop)
      · refine Cofan.IsColimit.hom_ext h₂ _ _ (fun a => by aesop))

Depends on / 依赖: Category, Category.assoc, Cofan.IsColimit.desc, Cofan.IsColimit.fac, Cofan.IsColimit.hom_ext, Cofan.IsColimit.mk, Cofan.mk_, IsColimit, cofan_mk_inj, combPairHoms, h.fac, hom_ext, s.inj
-/
def combPairIsColimit : IsColimit (Cofan.mk bc.pt (combPairHoms c₁ c₂ bc)) :=
  Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc h <| fun i => by
      cases i
      · exact Cofan.IsColimit.desc h₁ (fun a => s.inj (.inl a))
      · exact Cofan.IsColimit.desc h₂ (fun a => s.inj (.inr a)))
    (fun s w => by
      cases w <;>
      · simp only [cofan_mk_inj, combPairHoms, Category.assoc]
        erw [h.fac]
        simp only [Cofan.mk_ι_app, Cofan.IsColimit.fac])
    (fun s m hm => Cofan.IsColimit.hom_ext h _ _ <| fun w => by
      cases w
      · refine Cofan.IsColimit.hom_ext h₁ _ _ (fun a => by aesop)
      · refine Cofan.IsColimit.hom_ext h₂ _ _ (fun a => by aesop))

end Cofan

end Limits

end CategoryTheory
