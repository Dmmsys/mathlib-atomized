/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
module

public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Functors

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (Pre)Sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraperPresheaf`: `skyscraperPresheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraperSheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraperPresheafStalkOfSpecializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `A`.
* `skyscraperPresheafStalkOfNotSpecializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
TODO(@joelriou): refactor the definitions in this file so as to make them
particular cases of general constructions for points of sites from
`Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`.

-/

@[expose] public section

noncomputable section

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v w

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]

section

variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)

/-- A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
/-
**skyscraperPresheaf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheaf : Presheaf C X where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is 
a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if 
`p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
def skyscraperPresheaf : Presheaf C X where
  obj U := if p₀ ∈ unop U then A else terminal C
  map {U V} i :=
    if h : p₀ ∈ unop V then eqToHom <| by rw [if_pos h, if_pos (by simpa using i.unop.le h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
  map_comp {U V W} iVU iWV := by
    by_cases hW : p₀ ∈ unop W
    · have hV : p₀ ∈ unop V := leOfHom iWV.unop hW
      simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
    · dsimp; rw [dif_neg hW]; apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext
/-
**skyscraperPresheaf_eq_pushforward** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skyscraperPresheaf_eq_pushforward [hd : forall U : Opens (TopCat.of PUnit.
{u + 1}), Decidable (PUnit.unit in U)] : skyscraperPresheaf p₀ A = (ofHom (Conti
nuousMap.const (TopCat.of PUnit) p₀)) _* skyscraperPresheaf (X
参数：TopCat.of PUnit.{u + 1}；PUnit.unit in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem skyscraperPresheaf_eq_pushforward
    [hd : ∀ U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U)] :
    skyscraperPresheaf p₀ A =
      (ofHom (ContinuousMap.const (TopCat.of PUnit) p₀)) _*
        skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ofHom <|
      ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr

set_option backward.defeqAttrib.useBackward true in
/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
/-
**SkyscraperPresheafFunctor.map'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) : skyscraperPresheaf 
p₀ a ⟶ skyscraperPresheaf p₀ b where app U
参数：f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defin
es a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = 
f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) :
    skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app U :=
    if h : p₀ ∈ U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom i.unop hV
      simp only [skyscraperPresheaf_obj, hU, hV, ↓reduceDIte, eqToHom_trans_assoc, Category.assoc,
        eqToHom_trans]
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext

set_option backward.defeqAttrib.useBackward true in
/-
**SkyscraperPresheafFunctor.map'_id** 是 Mathlib 中的一个定理，位于命名空间 `SkyscraperPreshea
fFunctor`。
形式化陈述：∀ {X : TopCat} (p₀ : ↑X) [inst : (U : TopologicalSpace.Opens ↑X) → Decidab
le (p₀ ∈ U)] {C : Type v}   [inst_1 : CategoryTheory.Category.{w, v} C] [inst_2 
: CategoryTheory.Limits.HasTerminal C] {a : C},   SkyscraperPresheafFunctor.map'
 p₀ (CategoryTheory.CategoryStruct.id a) =     CategoryTheory.CategoryStruct.id 
(skyscraperPresheaf p₀ a)
参数：p₀ : ↑X；U : TopologicalSpace.Opens ↑X；p₀ ∈ U；CategoryTheory.CategoryStruct.id
 a；skyscraperPresheaf p₀ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.eqToHom_naturality`：eqToHom_naturality {f g : β -> C} (z 
: forall b, f b ⟶ g b) {j j' : β} (w : j = j') : z j ≫ eqToHom (by simp [w]) = e
qToHom (by simp [w]) ≫ …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `CategoryTheory.Limits.IsTerminal.from_self`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsTerminal X)
,   t.from X = CategoryTheory.Ca…
-/
theorem SkyscraperPresheafFunctor.map'_id {a : C} :
    SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]; split_ifs <;> cat_disch

set_option backward.defeqAttrib.useBackward true in
/-
**SkyscraperPresheafFunctor.map'_comp** 是 Mathlib 中的一个定理，位于命名空间 `SkyscraperPresh
eafFunctor`。
形式化陈述：∀ {X : TopCat} (p₀ : ↑X) [inst : (U : TopologicalSpace.Opens ↑X) → Decidab
le (p₀ ∈ U)] {C : Type v}   [inst_1 : CategoryTheory.Category.{w, v} C] [inst_2 
: CategoryTheory.Limits.HasTerminal C] {a b c : C} (f : a ⟶ b)   (g : b ⟶ c),   
SkyscraperPresheafFunctor.map' p₀ (CategoryTheory.CategoryStruct.comp f g) =    
 CategoryTheory.CategoryStruct.comp (SkyscraperPresheafFunctor.map' p₀ f) (Skysc
raperPresheafFunctor.map' p₀ g)
参数：p₀ : ↑X；U : TopologicalSpace.Opens ↑X；p₀ ∈ U；f : a ⟶ b；g : b ⟶ c；CategoryTheo
ry.CategoryStruct.comp f g；SkyscraperPresheafFunctor.map' p₀ f；SkyscraperPreshea
fFunctor.map' p₀ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
-/
theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]
  split_ifs with h <;> cat_disch

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
/-
**skyscraperPresheafFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafFunctor : C ⥤ Presheaf C X where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SkyscraperPresheafFunctor.map'_id`：∀ {X : TopCat} (p₀ : ↑X) [inst : (U :
 TopologicalSpace.Opens ↑X) → Decidable (p₀ ∈ U)] {C : Type v}   [inst_1 : Categ
oryTheory.Category.{w, …
· 使用定理 `SkyscraperPresheafFunctor.map'_comp`：∀ {X : TopCat} (p₀ : ↑X) [inst : (U
 : TopologicalSpace.Opens ↑X) → Decidable (p₀ ∈ U)] {C : Type v}   [inst_1 : Cat
egoryTheory.Category.{w, …

--- 原说明 ---
Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defin
es a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = 
f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps]
/-
**skyscraperPresheafCoconeOfSpecializes** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) : Cocone ((Open
Nhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where pt
参数：h : p₀ ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ c
losure {p₀}`
-/
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, unop_op,
            Functor.const_obj_obj, eqToHom_trans, Functor.const_obj_map, Category.comp_id] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
/-
**skyscraperPresheafCoconeIsColimitOfSpecializes** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) : IsCo
limit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where desc c
参数：h : p₀ ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ c
losure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc c := eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp
    rw [← c.w (homOfLE <| (le_top : unop U ≤ _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, op_unop]
    · exact h.mem_open U.unop.1.2 U.unop.2
  uniq c f h := by
    dsimp
    rw [← h, skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

/-- If `y ∈ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is `A`.
-/
/-
**skyscraperPresheafStalkOfSpecializes** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) 
: (skyscraperPresheaf p₀ A).stalk y ≅ A
参数：h : p₀ ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `y ∈ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is `A`
.
-/
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

@[reassoc (attr := simp)]
/-
**germ_skyscraperPresheafStalkOfSpecializes_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：germ_skyscraperPresheafStalkOfSpecializes_hom [HasColimits C] {y : X} (h :
 p₀ ⤳ y) (U hU) : (skyscraperPresheaf p₀ A).germ U y hU ≫ (skyscraperPresheafSta
lkOfSpecializes p₀ A h).hom = eqToHom (if_pos (h.mem_open U.2 hU))
参数：h : p₀ ⤳ y；U hU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma germ_skyscraperPresheafStalkOfSpecializes_hom [HasColimits C] {y : X} (h : p₀ ⤳ y) (U hU) :
    (skyscraperPresheaf p₀ A).germ U y hU ≫
      (skyscraperPresheafStalkOfSpecializes p₀ A h).hom = eqToHom (if_pos (h.mem_open U.2 hU)) :=
  colimit.isoColimitCocone_ι_hom _ _

/-- The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps]
/-
**skyscraperPresheafCocone** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafCocone (y : X) : Cocone ((OpenNhds.inclusion y).op ⋙ sky
scraperPresheaf p₀ A) where pt
参数：y : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ c
losure {p₀}`
-/
def skyscraperPresheafCocone (y : X) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
/-
**skyscraperPresheafCoconeIsColimitOfNotSpecializes** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) : 
IsColimit (skyscraperPresheafCocone p₀ A y)
参数：h : ¬p₀ ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ c
losure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : ∃ U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w (homOfLE <| @inf_le_left _ _ h1.choose U.unop).op, ←
        c.w (homOfLE <| @inf_le_right _ _ h1.choose U.unop).op, ← Category.assoc]
      congr 1
      refine ((if_neg ?_).symm.ndrec terminalIsTerminal).hom_ext _ _
      exact fun h => h1.choose_spec h.1
    uniq := fun c f H => by
      dsimp
      rw [← Category.id_comp f, ← H, ← Category.assoc]
      congr 1; apply terminalIsTerminal.hom_ext }

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
/-
**skyscraperPresheafStalkOfNotSpecializes** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳
 y) : (skyscraperPresheaf p₀ A).stalk y ≅ terminal C
参数：h : ¬p₀ ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is iso
morphic to a
terminal object.
-/
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is a terminal object
-/
/-
**skyscraperPresheafStalkOfNotSpecializesIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} 
(h : ¬p₀ ⤳ y) : IsTerminal ((skyscraperPresheaf p₀ A).stalk y)
参数：h : ¬p₀ ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is a t
erminal object
-/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
  IsTerminal.ofIso terminalIsTerminal <| (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm
/-
**skyscraperPresheaf_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.Presheaf.isSheaf_iso_iff`：isSheaf_iso_iff {F G : Presheaf C X} (α
 : F ≅ G) : F.IsSheaf ↔ G.IsSheaf
· 使用定理 `skyscraperPresheaf_eq_pushforward`：skyscraperPresheaf_eq_pushforward [hd
 : forall U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit in U)] : sk
yscraperPresheaf p₀ A =…
· 使用定理 `TopCat.Sheaf.pushforward_sheaf_of_sheaf`：pushforward_sheaf_of_sheaf {F :
 X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf
· 使用定理 `TopCat.Presheaf.isSheaf_on_punit_of_isTerminal`：isSheaf_on_punit_of_isTe
rminal (F : Presheaf C (TopCat.of PUnit)) (it : IsTerminal <| F.obj <| op ⊥) : F
.IsSheaf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical exact
    (Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr <|
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
          · #adaptation_note /-- 2024-03-24
            Previously the universe annotation was not needed here. -/
            exact Set.notMem_empty PUnit.unit.{u + 1})))

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
@[simps!]
/-
**skyscraperSheaf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperSheaf : Sheaf C X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `skyscraperPresheaf_isSheaf`：skyscraperPresheaf_isSheaf : (skyscraperPres
heaf p₀ A).IsSheaf

--- 原说明 ---
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assig
ns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
def skyscraperSheaf : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩

/-- Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
/-
**skyscraperSheafFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperSheafFunctor : C ⥤ Sheaf C X where obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines 
a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = 
f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraperSheafFunctor : C ⥤ Sheaf C X where
  obj c := skyscraperSheaf p₀ c
  map f := ObjectProperty.homMk <| (skyscraperPresheafFunctor p₀).map f
  map_id _ := Sheaf.hom_ext <| (skyscraperPresheafFunctor p₀).map_id _
  map_comp _ _ := Sheaf.hom_ext <| (skyscraperPresheafFunctor p₀).map_comp _ _

namespace StalkSkyscraperPresheafAdjunctionAuxs

variable [HasColimits C]

set_option backward.defeqAttrib.useBackward true in
/-- If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraperPresheaf p₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a terminal object
if `p₀ ∉ U`.
-/
@[simps]
/-
**StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf** 是 Mathlib 中的一个定义，
位于命名空间 `StalkSkyscraperPresheafAdjunctionAuxs`。
形式化陈述：toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) : 𝓕 ⟶
 skyscraperPresheaf p₀ c where app U
参数：f : 𝓕.stalk p₀ ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraperPresheaf p
₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a 
terminal object
if `p₀ ∉ U`.
-/
def toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    𝓕 ⟶ skyscraperPresheaf p₀ c where
  app U :=
    if h : p₀ ∈ U.unop then 𝓕.germ _ p₀ h ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    dsimp
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom inc.unop hV
      split_ifs
      rw [← Category.assoc, 𝓕.germ_res' inc, Category.assoc, Category.assoc, eqToHom_trans]
    · split_ifs
      exact ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `f : 𝓕 ⟶ skyscraperPresheaf p₀ c` is a natural transformation, then there is a morphism
`𝓕.stalk p₀ ⟶ c` defined as the morphism from colimit to cocone at `c`.
-/
/-
**StalkSkyscraperPresheafAdjunctionAuxs.fromStalk** 是 Mathlib 中的一个定义，位于命名空间 `Sta
lkSkyscraperPresheafAdjunctionAuxs`。
形式化陈述：fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕
.stalk p₀ ⟶ c
参数：f : 𝓕 ⟶ skyscraperPresheaf p₀ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : 𝓕 ⟶ skyscraperPresheaf p₀ c` is a natural transformation, then there is 
a morphism
`𝓕.stalk p₀ ⟶ c` defined as the morphism from colimit to cocone at `c`.
-/
def fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕.stalk p₀ ⟶ c :=
  let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
    Cocone.mk c <|
      { app := fun U => f.app ((OpenNhds.inclusion p₀).op.obj U) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map,
            Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj]
          rw [Category.comp_id, ← Category.assoc, comp_eqToHom_iff, Category.assoc,
            eqToHom_trans, f.naturality, skyscraperPresheaf_map]
          have hV : p₀ ∈ (OpenNhds.inclusion p₀).obj V.unop := V.unop.2
          simp only [dif_pos hV] }
  colimit.desc _ χ

@[reassoc (attr := simp)]
/-
**StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk** 是 Mathlib 中的一个引理，位于命名空间
 `StalkSkyscraperPresheafAdjunctionAuxs`。
形式化陈述：germ_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c
) (U) (hU) : 𝓕.germ U p₀ hU ≫ fromStalk p₀ f = f.app (op U) ≫ eqToHom (if_pos hU
)
参数：f : 𝓕 ⟶ skyscraperPresheaf p₀ c；U；hU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
lemma germ_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU) :
    𝓕.germ U p₀ hU ≫ fromStalk p₀ f = f.app (op U) ≫ eqToHom (if_pos hU) :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**StalkSkyscraperPresheafAdjunctionAuxs.to_skyscraper_fromStalk** 是 Mathlib 中的一个
定理，位于命名空间 `StalkSkyscraperPresheafAdjunctionAuxs`。
形式化陈述：to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPres
heaf p₀ c) : toSkyscraperPresheaf p₀ (fromStalk _ f) = f
参数：f : 𝓕 ⟶ skyscraperPresheaf p₀ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk_assoc`：∀ {X : TopCa
t} (p₀ : ↑X) [inst : (U : TopologicalSpace.Opens ↑X) → Decidable (p₀ ∈ U)] {C : 
Type v}   [inst_1 : CategoryTheory.Category.{u, …
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) :
    toSkyscraperPresheaf p₀ (fromStalk _ f) = f := by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  · simp
  · exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..

set_option backward.isDefEq.respectTransparency.types false in
/-
**StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper** 是 Mathlib 中的一个
定理，位于命名空间 `StalkSkyscraperPresheafAdjunctionAuxs`。
形式化陈述：fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) : 
fromStalk p₀ (toSkyscraperPresheaf _ f) = f
参数：f : 𝓕.stalk p₀ ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk`：germ_fromStalk {𝓕 
: Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU) : 𝓕.germ U p₀
 hU ≫ fromStalk p₀ f = f.app (op U) ≫ eqTo…
· 使用定理 `StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app`：∀ {X : T
opCat} (p₀ : ↑X) [inst : (U : TopologicalSpace.Opens ↑X) → Decidable (p₀ ∈ U)] {
C : Type v}   [inst_1 : CategoryTheory.Category.{u, …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `TopCat.Presheaf.germ.eq_1`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (F : T
opCat.Presheaf …
-/
theorem fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    fromStalk p₀ (toSkyscraperPresheaf _ f) = f := by
  refine 𝓕.stalk_hom_ext fun U hxU ↦ ?_
  rw [germ_fromStalk, toSkyscraperPresheaf_app, dif_pos hxU, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, Presheaf.germ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
/-
**StalkSkyscraperPresheafAdjunctionAuxs.unit** 是 Mathlib 中的一个定义，位于命名空间 `StalkSky
scraperPresheafAdjunctionAuxs`。
形式化陈述：{X : TopCat} →   (p₀ : ↑X) →     [inst : (U : TopologicalSpace.Opens ↑X) →
 Decidable (p₀ ∈ U)] →       {C : Type v} →         [inst_1 : CategoryTheory.Cat
egory.{u, v} C] →           [inst_2 : CategoryTheory.Limits.HasTerminal C] →    
         [inst_3 : CategoryTheory.Limits.HasColimits C] →               Category
Theory.Functor.id (TopCat.Presheaf C X) ⟶                 (TopCat.Presheaf.stalk
Functor C p₀).comp (skyscraperPresheafFunctor p₀)
参数：p₀ : ↑X；U : TopologicalSpace.Opens ↑X；p₀ ∈ U；TopCat.Presheaf C X；TopCat.Presh
eaf.stalkFunctor C p₀；skyscraperPresheafFunctor p₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
protected def unit :
    𝟭 (Presheaf C X) ⟶ Presheaf.stalkFunctor C p₀ ⋙ skyscraperPresheafFunctor p₀ where
  app _ := toSkyscraperPresheaf _ <| 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkFunctor_obj]
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
/-
**StalkSkyscraperPresheafAdjunctionAuxs.counit** 是 Mathlib 中的一个定义，位于命名空间 `StalkS
kyscraperPresheafAdjunctionAuxs`。
形式化陈述：{X : TopCat} →   (p₀ : ↑X) →     [inst : (U : TopologicalSpace.Opens ↑X) →
 Decidable (p₀ ∈ U)] →       {C : Type v} →         [inst_1 : CategoryTheory.Cat
egory.{u, v} C] →           [inst_2 : CategoryTheory.Limits.HasTerminal C] →    
         [inst_3 : CategoryTheory.Limits.HasColimits C] →               (skyscra
perPresheafFunctor p₀).comp (TopCat.Presheaf.stalkFunctor C p₀) ⟶ CategoryTheory
.Functor.id C
参数：p₀ : ↑X；U : TopologicalSpace.Opens ↑X；p₀ ∈ U；skyscraperPresheafFunctor p₀；Top
Cat.Presheaf.stalkFunctor C p₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
protected def counit :
    skyscraperPresheafFunctor p₀ ⋙ (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⟶ 𝟭 C where
  app c := (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ by simp [hxU]

end StalkSkyscraperPresheafAdjunctionAuxs

section

open StalkSkyscraperPresheafAdjunctionAuxs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `skyscraperPresheafFunctor` is the right adjoint of `Presheaf.stalkFunctor`
-/
/-
**skyscraperPresheafStalkAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperPresheafStalkAdjunction [HasColimits C] : (Presheaf.stalkFunctor
 C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`skyscraperPresheafFunctor` is the right adjoint of `Presheaf.stalkFunctor`
-/
def skyscraperPresheafStalkAdjunction [HasColimits C] :
    (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where
  unit := StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  left_triangle_components X := by
    dsimp [Presheaf.stalkFunctor, toSkyscraperPresheaf]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, ι_colimMap_assoc, skyscraperPresheaf_obj,
      Functor.whiskerLeft_app, Category.comp_id]
    split_ifs with h
    · simp [skyscraperPresheafStalkOfSpecializes]
      rfl
    · simp only [skyscraperPresheafStalkOfSpecializes, colimit.isoColimitCocone_ι_hom,
        skyscraperPresheafCoconeOfSpecializes_pt, skyscraperPresheafCoconeOfSpecializes_ι_app,
        Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, Functor.const_obj_obj]
      rw [comp_eqToHom_iff]
      apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
  right_triangle_components Y := by
    ext
    simp only [skyscraperPresheafFunctor_obj, Functor.id_obj, skyscraperPresheaf_obj,
      Presheaf.stalkFunctor_obj, unit_app, counit_app,
      skyscraperPresheafStalkOfSpecializes, skyscraperPresheafFunctor_map, Presheaf.comp_app,
      toSkyscraperPresheaf_app, Category.id_comp, SkyscraperPresheafFunctor.map'_app]
    split_ifs with h
    · simp [Presheaf.germ]
      rfl
    · simp
      rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : (skyscraperPresheafFunctor p₀ : C ⥤ Presheaf C X).IsRightAdjoint :=
  (skyscraperPresheafStalkAdjunction _).isRightAdjoint
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : (Presheaf.stalkFunctor C p₀).IsLeftAdjoint :=
  -- Use a classical instance instead of the one from `variable`s
  have : ∀ U : Opens X, Decidable (p₀ ∈ U) := fun _ ↦ Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint

/-- Taking stalks of a sheaf is the left adjoint functor to `skyscraperSheafFunctor`
-/
/-
**stalkSkyscraperSheafAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stalkSkyscraperSheafAdjunction [HasColimits C] : Sheaf.forget C X ⋙ Preshe
af.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where -- Porting note (https://
github.com/leanprover-community/mathlib4/issues/11041): `ext1` is changed to `Sh
eaf.Hom.ext`, unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking stalks of a sheaf is the left adjoint functor to `skyscraperSheafFunctor`
-/
def stalkSkyscraperSheafAdjunction [HasColimits C] :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext1` is changed to `Sheaf.Hom.ext`,
  unit :=
    { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
      naturality := fun 𝓐 𝓑 f => Sheaf.hom_ext <| by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  left_triangle_components X :=
    ((skyscraperPresheafStalkAdjunction p₀).left_triangle_components X.obj)
  right_triangle_components _ :=
    Sheaf.hom_ext ((skyscraperPresheafStalkAdjunction p₀).right_triangle_components _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : (Sheaf.forget C X ⋙ Presheaf.stalkFunctor C p₀).IsLeftAdjoint :=
  have : ∀ U : Opens X, Decidable (p₀ ∈ U) := fun _ ↦ Classical.dec _
  (stalkSkyscraperSheafAdjunction p₀).isLeftAdjoint
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : (skyscraperSheafFunctor p₀ : C ⥤ Sheaf C X).IsRightAdjoint :=
  (stalkSkyscraperSheafAdjunction _).isRightAdjoint

/-- Taking stalks is the left adjoint of `skyscraperSheafFunctor ⋙ Sheaf.forget`. Useful
only when the fact that `skyscraperPresheafFunctor` factors through `Sheaf C X` is relevant. -/
/-
**skyscraperSheafForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skyscraperSheafForgetAdjunction [HasColimits C] : Presheaf.stalkFunctor C 
p₀ ⊣ skyscraperSheafFunctor p₀ ⋙ Sheaf.forget C X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking stalks is the left adjoint of `skyscraperSheafFunctor ⋙ Sheaf.forget`. Us
eful
only when the fact that `skyscraperPresheafFunctor` factors through `Sheaf C X` 
is relevant.
-/
noncomputable def skyscraperSheafForgetAdjunction [HasColimits C] :
    Presheaf.stalkFunctor C p₀ ⊣ skyscraperSheafFunctor p₀ ⋙ Sheaf.forget C X :=
  skyscraperPresheafStalkAdjunction p₀

set_option backward.defeqAttrib.useBackward true in
variable {A p₀} in
/--
On an open set not containing `p₀`, the value of skyscraper sheaf supported at `p₀` is a terminal
object.
-/
noncomputable
/-
**isTerminalSkyscraperSheafObjObjOfNotMem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isTerminalSkyscraperSheafObjObjOfNotMem {U : (Opens X)ᵒᵖ} (h : p₀ ∉ unop U
) : IsTerminal ((skyscraperSheaf p₀ A).obj.obj U)
参数：Opens X；h : p₀ ∉ unop U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isTerminalSkyscraperSheafObjObjOfNotMem {U : (Opens X)ᵒᵖ} (h : p₀ ∉ unop U) :
    IsTerminal ((skyscraperSheaf p₀ A).obj.obj U) := by
  dsimp
  rw [if_neg h]
  exact terminalIsTerminal

end

end

