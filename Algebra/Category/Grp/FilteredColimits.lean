/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ GrpCat`.
We show that the colimit of `F ⋙ forget₂ GrpCat MonCat` (in `MonCat`) carries the structure of a
group,
thereby showing that the forgetful functor `forget₂ GrpCat MonCat` preserves filtered colimits.
In particular, this implies that `forget GrpCat` preserves filtered colimits.
Similarly for `AddGrpCat`, `CommGrpCat` and `AddCommGrpCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace GrpCat.FilteredColimits

section

-- Mathlib3 used parameters here, mainly so we could have the abbreviations `G` and `G.mk` below,
-- without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

/-- The colimit of `F ⋙ forget₂ GrpCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive
  /-- The colimit of `F ⋙ forget₂ AddGrpCat AddMonCat` in the category `AddMonCat`.
  In the following, we will show that this has the structure of an additive group. -/]
/-
**GrpCat.FilteredColimits.G** 是 Mathlib 中的一个缩写定义，位于命名空间 `GrpCat.FilteredColimits
`。
形式化陈述：G : MonCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev G : MonCat :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ GrpCat MonCat.{max v u})

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive /-- The canonical projection into the colimit, as a quotient type. -/]
/-
**GrpCat.FilteredColimits.G.mk** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.FilteredColimit
s.G`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     [inst_1 : C
ategoryTheory.IsFiltered J] →       (F : CategoryTheory.Functor J GrpCat) → (j :
 J) × ↑(F.obj j) → ↑(GrpCat.FilteredColimits.G F)
参数：F : CategoryTheory.Functor J GrpCat；j : J；F.obj j；GrpCat.FilteredColimits.G F
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection into the colimit, as a quotient type.
-/
abbrev G.mk : (Σ j, F.obj j) → G.{v, u} F :=
  fun x ↦ (F ⋙ forget GrpCat).ιColimitType x.1 x.2

@[to_additive]
/-
**GrpCat.FilteredColimits.G.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.FilteredColi
mits.G`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.SmallCategory J] [inst_1 : CategoryT
heory.IsFiltered J]   (F : CategoryTheory.Functor J GrpCat) (x y : (j : J) × ↑(F
.obj j)),   (∃ k f g,       (CategoryTheory.ConcreteCategory.hom (F.map f)) x.sn
d = (CategoryTheory.ConcreteCategory.hom (F.map g)) y.snd) →     GrpCat.Filtered
Colimits.G.mk F x = GrpCat.FilteredColimits.G.mk F y
参数：F : CategoryTheory.Functor J GrpCat；x y : (j : J) × ↑(F.obj j)；∃ k f g,      
 (CategoryTheory.ConcreteCategory.hom (F.map f)) x.snd = (CategoryTheory.Concret
eCategory.hom (F.map g)) y.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eqvGen_sound`：Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = 
Quot.mk r b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
`：eqvGen_colimitTypeRel_of_rel (x y : Σ j, F.obj j) : FilteredColimit.Rel.{v, u}
 F x y -> Relation.EqvGen F.ColimitTypeRel x y
-/
theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    G.mk.{v, u} F x = G.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget GrpCat) x y h)

@[to_additive]
/-
**GrpCat.FilteredColimits.colimit_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Filte
redColimits`。
形式化陈述：colimit_one_eq (j : J) : (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonCat.FilteredColimits.colimit_one_eq`：colimit_one_eq (j : J) : (1 : M.
{v, u} F) = M.mk F ⟨j, 1⟩
-/
theorem colimit_one_eq (j : J) : (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩ :=
  MonCat.FilteredColimits.colimit_one_eq _ _

@[to_additive]
/-
**GrpCat.FilteredColimits.colimit_mul_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Fi
lteredColimits`。
形式化陈述：colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k)
 : G.mk.{v, u} F x * G.mk F y = G.mk F ⟨k, F.map f x.2 * F.map g y.2⟩
参数：x y : Σ j, F.obj j；k : J；f : x.1 ⟶ k；g : y.1 ⟶ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonCat.FilteredColimits.colimit_mul_mk_eq`：colimit_mul_mk_eq (x y : Σ j,
 F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) : M.mk.{v, u} F x * M.mk F y = M.m
k F ⟨k, F.map f x.2 * F.map g y…
-/
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    G.mk.{v, u} F x * G.mk F y = G.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ :=
  MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

@[to_additive]
/-
**GrpCat.FilteredColimits.colimit_mul_mk_eq'** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat.F
ilteredColimits`。
形式化陈述：colimit_mul_mk_eq' {j : J} (x y : F.obj j) : G.mk.{v, u} F ⟨j, x⟩ * G.mk.{
v, u} F ⟨j, y⟩ = G.mk.{v, u} F ⟨j, x * y⟩
参数：x y : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GrpCat.FilteredColimits.colimit_mul_mk_eq`：colimit_mul_mk_eq (x y : Σ j,
 F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) : G.mk.{v, u} F x * G.mk F y = G.m
k F ⟨k, F.map f x.2 * F.map g y…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
-/
lemma colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    G.mk.{v, u} F ⟨j, x⟩ * G.mk.{v, u} F ⟨j, y⟩ = G.mk.{v, u} F ⟨j, x * y⟩ := by
  #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  `simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  have := colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  simpa using this

/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive /-- The "unlifted" version of negation in the colimit. -/]
/-
**GrpCat.FilteredColimits.colimitInvAux** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.Filter
edColimits`。
形式化陈述：colimitInvAux (x : Σ j, F.obj j) : G.{v, u} F
参数：x : Σ j, F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "unlifted" version of taking inverses in the colimit.
-/
def colimitInvAux (x : Σ j, F.obj j) : G.{v, u} F :=
  G.mk F ⟨x.1, x.2⁻¹⟩

@[to_additive]
/-
**GrpCat.FilteredColimits.colimitInvAux_eq_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `Grp
Cat.FilteredColimits`。
形式化陈述：colimitInvAux_eq_of_rel (x y : Σ j, F.obj j) (h : Types.FilteredColimit.Re
l (F ⋙ forget GrpCat) x y) : colimitInvAux.{v, u} F x = colimitInvAux F y
参数：x y : Σ j, F.obj j；h : Types.FilteredColimit.Rel (F ⋙ forget GrpCat) x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GrpCat.FilteredColimits.G.mk_eq`：∀ {J : Type v} [inst : CategoryTheory.S
mallCategory J] [inst_1 : CategoryTheory.IsFiltered J]   (F : CategoryTheory.Fun
ctor J GrpCat) (x y :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
-/
theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget GrpCat) x y) :
    colimitInvAux.{v, u} F x = colimitInvAux F y := by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv, map_inv, inv_inj]
  exact hfg

/-- Taking inverses in the colimit. See also `colimitInvAux`. -/
@[to_additive /-- Negation in the colimit. See also `colimitNegAux`. -/]
/-
**GrpCat.FilteredColimits.colimitInv** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat.FilteredC
olimits`。
形式化陈述：colimitInv : Inv (G.{v, u} F) where inv x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking inverses in the colimit. See also `colimitInvAux`.
-/
instance colimitInv : Inv (G.{v, u} F) where
  inv x := by
    refine Quot.lift (colimitInvAux.{v, u} F) ?_ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

@[to_additive (attr := simp)]
/-
**GrpCat.FilteredColimits.colimit_inv_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Fi
lteredColimits`。
形式化陈述：colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, 
x.2⁻¹⟩
参数：x : Σ j, F.obj j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩ :=
  rfl

@[to_additive]
/-
**GrpCat.FilteredColimits.colimitGroup** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat.Filtere
dColimits`。
形式化陈述：colimitGroup : Group (G.{v, u} F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance colimitGroup : Group (G.{v, u} F) :=
  { colimitInv.{v, u} F, (G.{v, u} F).str with
    inv_mul_cancel := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      change (G.mk _ _)⁻¹ * G.mk _ _ = _
      obtain ⟨j, x⟩ := x
      simp [colimit_inv_mk_eq, colimit_mul_mk_eq F ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq F j] }

/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive /-- The bundled additive group giving the filtered colimit of a diagram. -/]
/-
**GrpCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.FilteredColi
mits`。
形式化陈述：colimit : GrpCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled group giving the filtered colimit of a diagram.
-/
noncomputable def colimit : GrpCat.{max v u} :=
  GrpCat.of (G.{v, u} F)

/-- The cocone over the proposed colimit group. -/
@[to_additive /-- The cocone over the proposed colimit additive group. -/]
/-
**GrpCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.Filter
edColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit group.
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app J := GrpCat.ofHom ((MonCat.FilteredColimits.colimitCocone
    (F ⋙ forget₂ GrpCat MonCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ MonCat).map_injective
    ((MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ GrpCat MonCat)).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `GrpCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddGroup`. -/]
/-
**GrpCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `GrpC
at.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `GrpCat`.
-/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ _ MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ GrpCat MonCat))

@[to_additive forget₂AddMon_preservesFilteredColimits]
/-
**GrpCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat.FilteredColim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits.{u} (forget₂ GrpCat.{u} MonCat.{u}) where
      preserves_filtered_colimits x hx1 _ :=
      letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩

@[to_additive]
/-
**GrpCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 中的一个实例，位于
命名空间 `GrpCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget GrpCa
t.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget GrpCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ GrpCat MonCat) (forget MonCat.{u})

end

end GrpCat.FilteredColimits

namespace CommGrpCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommGrpCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommGrpCat GrpCat` in the category `GrpCat`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive
  /-- The colimit of `F ⋙ forget₂ AddCommGrpCat AddGrpCat` in the category `AddGrpCat`.
  In the following, we will show that this has the structure of a _commutative_ additive group. -/]
/-
**CommGrpCat.FilteredColimits.G** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommGrpCat.Filtered
Colimits`。
形式化陈述：G : GrpCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev G : GrpCat.{max v u} :=
  GrpCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGrpCat.{max v u} GrpCat.{max v u})

@[to_additive]
/-
**CommGrpCat.FilteredColimits.colimitCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `CommGr
pCat.FilteredColimits`。
形式化陈述：colimitCommGroup : CommGroup.{max v u} (G.{v, u} F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance colimitCommGroup : CommGroup.{max v u} (G.{v, u} F) :=
  { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGrpCat CommMonCat.{max v u}) with }

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive
/-- The bundled additive commutative group giving the filtered colimit of a diagram. -/]
/-
**CommGrpCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat.Filt
eredColimits`。
形式化陈述：colimit : CommGrpCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def colimit : CommGrpCat :=
  CommGrpCat.of (G.{v, u} F)

/-- The cocone over the proposed colimit commutative group. -/
@[to_additive /-- The cocone over the proposed colimit additive commutative group. -/]
/-
**CommGrpCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCa
t.FilteredColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit commutative group.
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app J := CommGrpCat.ofHom
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ GrpCat).map_injective
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `CommGrpCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddCommGroup`. -/]
/-
**CommGrpCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `
CommGrpCat.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `CommGrpCat`.
-/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ _ GrpCat)
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrpCat GrpCat))

@[to_additive]
/-
**CommGrpCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat.Filte
redColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget₂Group_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommGrpCat GrpCat.{u}) where
  preserves_filtered_colimits J hJ1 _ :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGrpCat GrpCat.{u})) }

@[to_additive]
/-
**CommGrpCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 中的一个实
例，位于命名空间 `CommGrpCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget CommG
rpCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommGrpCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommGrpCat GrpCat) (forget GrpCat.{u})

end

end CommGrpCat.FilteredColimits

