/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → Opens X` we can form the subcategory
`{ V : Opens X // ∃ i, V ≤ U i }`, which has `iSup U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## Main statement

`TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`: for a presheaf on a topological space,
the sheaf condition in terms of Grothendieck topology is equivalent to the `OpensLeCover`
sheaf condition. This result will be used to further connect to other sheaf conditions on spaces,
like `pairwise_intersections` and `equalizer_products`.

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/

@[expose] public section


universe w

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

variable {C : Type*} [Category* C]
variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type*} (U : ι → Opens X)

namespace Presheaf

namespace SheafCondition

/-- The category of open sets contained in some element of the cover.
-/
/-
**TopCat.Presheaf.SheafCondition.OpensLeCover** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.
Presheaf.SheafCondition`。
形式化陈述：OpensLeCover : Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of open sets contained in some element of the cover.
-/
def OpensLeCover : Type w :=
  ObjectProperty.FullSubcategory fun V : Opens X ↦ ∃ i, V ≤ U i
deriving Category
/-
**TopCat.Presheaf.SheafCondition.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf.She
afCondition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Nonempty ι] : Inhabited (OpensLeCover U) :=
  ⟨⟨⊥, let ⟨i⟩ := h; ⟨i, bot_le⟩⟩⟩

namespace OpensLeCover

variable {U}

/-- An arbitrarily chosen index such that `V ≤ U i`.
-/
/-
**TopCat.Presheaf.SheafCondition.OpensLeCover.index** 是 Mathlib 中的一个定义，位于命名空间 `T
opCat.Presheaf.SheafCondition.OpensLeCover`。
形式化陈述：index (V : OpensLeCover U) : ι
参数：V : OpensLeCover U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrarily chosen index such that `V ≤ U i`.
-/
def index (V : OpensLeCover U) : ι :=
  V.property.choose

/-- The morphism from `V` to `U i` for some `i`.
-/
/-
**TopCat.Presheaf.SheafCondition.OpensLeCover.homToIndex** 是 Mathlib 中的一个定义，位于命名
空间 `TopCat.Presheaf.SheafCondition.OpensLeCover`。
形式化陈述：homToIndex (V : OpensLeCover U) : V.obj ⟶ U (index V)
参数：V : OpensLeCover U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from `V` to `U i` for some `i`.
-/
def homToIndex (V : OpensLeCover U) : V.obj ⟶ U (index V) :=
  V.property.choose_spec.hom

end OpensLeCover

/-- `iSup U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
/-
**TopCat.Presheaf.SheafCondition.opensLeCoverCocone** 是 Mathlib 中的一个定义，位于命名空间 `T
opCat.Presheaf.SheafCondition`。
形式化陈述：opensLeCoverCocone : Cocone (ObjectProperty.ι _ : OpensLeCover U ⥤ Opens X
) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iSup U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opensLeCoverCocone : Cocone (ObjectProperty.ι _ : OpensLeCover U ⥤ Opens X) where
  pt := iSup U
  ι := { app := fun V : OpensLeCover U => V.homToIndex ≫ Opens.leSupr U _ }

end SheafCondition

open SheafCondition

/-- An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`isSheaf_iff_isSheafOpensLeCover`).

A presheaf is a sheaf if `F` sends the cone `(opensLeCoverCocone U).op` to a limit cone.
(Recall `opensLeCoverCocone U`, has cone point `iSup U`,
mapping down to any `V` which is contained in some `U i`.)
-/
/-
**TopCat.Presheaf.IsSheafOpensLeCover** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf
`。
形式化陈述：IsSheafOpensLeCover : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`isSheaf_iff_isSheafOpensLeCover`).

A presheaf is a sheaf if `F` sends the cone `(opensLeCoverCocone U).op` to a lim
it cone.
(Recall `opensLeCoverCocone U`, has cone point `iSup U`,
mapping down to any `V` which is contained in some `U i`.)
-/
def IsSheafOpensLeCover : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (opensLeCoverCocone U).op))

section

variable {Y : Opens X}

/-- Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, we may
take the presieve on `Y` associated to `U` and the sieve generated by it, and form the
full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of arrows
in the sieve. This full subcategory is equivalent to `OpensLeCover U`, the (poset)
category of opens contained in some `U i`. -/
@[simps]
/-
**TopCat.Presheaf.generateEquivalenceOpensLe_functor'** 是 Mathlib 中的一个定义，位于命名空间 
`TopCat.Presheaf`。
形式化陈述：generateEquivalenceOpensLe_functor' : (ObjectProperty.FullSubcategory fun 
f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) ⥤ Opens
LeCover U where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, 
we may
take the presieve on `Y` associated to `U` and the sieve generated by it, and fo
rm the
full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of a
rrows
in the sieve. This full subcategory is equivalent to `OpensLeCover U`, the (pose
t)
category of opens contained in some `U i`.
-/
def generateEquivalenceOpensLe_functor' :
    (ObjectProperty.FullSubcategory
      fun f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) ⥤
    OpensLeCover U where
  obj f :=
    ⟨f.1.left,
      let ⟨_, h, _, ⟨i, hY⟩, _⟩ := f.2
      ⟨i, hY ▸ h.le⟩⟩
  map g := ObjectProperty.homMk g.hom.left

/-- Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, we may
take the presieve on `Y` associated to `U` and the sieve generated by it, and form the
full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of arrows
in the sieve. This full subcategory is equivalent to `OpensLeCover U`, the (poset)
category of opens contained in some `U i`. -/
@[simps]
/-
**TopCat.Presheaf.generateEquivalenceOpensLe_inverse'** 是 Mathlib 中的一个定义，位于命名空间 
`TopCat.Presheaf`。
形式化陈述：generateEquivalenceOpensLe_inverse' (hY : Y = iSup U) : OpensLeCover U ⥤ (
ObjectProperty.FullSubcategory fun f : Over Y => (Sieve.generate (presieveOfCove
ringAux U Y)).arrows f.hom) where obj
参数：hY : Y = iSup U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, 
we may
take the presieve on `Y` associated to `U` and the sieve generated by it, and fo
rm the
full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of a
rrows
in the sieve. This full subcategory is equivalent to `OpensLeCover U`, the (pose
t)
category of opens contained in some `U i`.
-/
def generateEquivalenceOpensLe_inverse' (hY : Y = iSup U) :
    OpensLeCover U ⥤
    (ObjectProperty.FullSubcategory fun f : Over Y =>
      (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) where
  obj := fun V => ⟨⟨V.obj, ⟨⟨⟩⟩, homOfLE <| hY ▸ (V.2.choose_spec.trans (le_iSup U (V.2.choose)))⟩,
    ⟨U V.2.choose, V.2.choose_spec.hom, homOfLE <| hY ▸ le_iSup U V.2.choose,
      ⟨V.2.choose, rfl⟩, rfl⟩⟩
  map g := ObjectProperty.homMk (Over.homMk g.hom)

/-- Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, we may
take the presieve on `Y` associated to `U` and the sieve generated by it, and form the
full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of arrows
in the sieve. This full subcategory is equivalent to `OpensLeCover U`, the (poset)
category of opens contained in some `U i`. -/
@[simps]
/-
**TopCat.Presheaf.generateEquivalenceOpensLe** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.P
resheaf`。
形式化陈述：generateEquivalenceOpensLe (hY : Y = iSup U) : (ObjectProperty.FullSubcate
gory fun f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom
) ≌ OpensLeCover U where functor
参数：hY : Y = iSup U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, 
we may
take the presieve on `Y` associated to `U` and the sieve generated by it, and fo
rm the
full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of a
rrows
in the sieve. This full subcategory is equivalent to `OpensLeCover U`, the (pose
t)
category of opens contained in some `U i`.
-/
def generateEquivalenceOpensLe (hY : Y = iSup U) :
    (ObjectProperty.FullSubcategory
      fun f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) ≌
    OpensLeCover U where
  functor := generateEquivalenceOpensLe_functor' _
  inverse := generateEquivalenceOpensLe_inverse' _ hY
  unitIso := eqToIso <| CategoryTheory.Functor.ext (by cat_disch)
  counitIso := eqToIso <| CategoryTheory.Functor.ext (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a family of opens `opensLeCoverCocone U` is essentially the natural cocone
associated to the sieve generated by the presieve associated to `U` with indexing
category changed using the above equivalence. -/
@[simps]
/-
**TopCat.Presheaf.whiskerIsoMapGenerateCocone** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.
Presheaf`。
形式化陈述：whiskerIsoMapGenerateCocone (hY : Y = iSup U) : (F.mapCone (opensLeCoverCo
cone U).op).whisker (generateEquivalenceOpensLe U hY).op.functor ≅ F.mapCone (Si
eve.generate (presieveOfCoveringAux U Y)).arrows.cocone.op where hom
参数：hY : Y = iSup U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of opens `opensLeCoverCocone U` is essentially the natural cocone
associated to the sieve generated by the presieve associated to `U` with indexin
g
category changed using the above equivalence.
-/
def whiskerIsoMapGenerateCocone (hY : Y = iSup U) :
    (F.mapCone (opensLeCoverCocone U).op).whisker (generateEquivalenceOpensLe U hY).op.functor ≅
      F.mapCone (Sieve.generate (presieveOfCoveringAux U Y)).arrows.cocone.op where
  hom :=
    { hom := F.map (eqToHom (congr_arg op hY.symm))
      w := fun j => by
        dsimp
        rw [← F.map_comp]
        congr 1 }
  inv :=
    { hom := F.map (eqToHom (congr_arg op hY))
      w := fun j => by
        dsimp
        rw [← F.map_comp]
        congr 1 }
  hom_inv_id := by
    ext
    simp [eqToHom_map]
  inv_hom_id := by
    ext
    simp [eqToHom_map]

/-- Given a presheaf `F` on the topological space `X` and a family of opens `U` of `X`,
the natural cone associated to `F` and `U` used in the definition of
`F.IsSheafOpensLeCover` is a limit cone iff the natural cone associated to `F`
and the sieve generated by the presieve associated to `U` is a limit cone. -/
/-
**TopCat.Presheaf.isLimitOpensLeEquivGenerate** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.
Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf `F` on the topological space `X` and a family of opens `U` of `
X`,
the natural cone associated to `F` and `U` used in the definition of
`F.IsSheafOpensLeCover` is a limit cone iff the natural cone associated to `F`
and the sieve generated by the presieve associated to `U` is a limit cone.
-/
def isLimitOpensLeEquivGenerate₁ (hY : Y = iSup U) :
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
      IsLimit (F.mapCone (Sieve.generate (presieveOfCoveringAux U Y)).arrows.cocone.op) :=
  (IsLimit.whiskerEquivalenceEquiv (generateEquivalenceOpensLe U hY).op).trans
    (IsLimit.equivIsoLimit (whiskerIsoMapGenerateCocone F U hY))

/-- Given a presheaf `F` on the topological space `X` and a presieve `R` whose generated sieve
is covering for the associated Grothendieck topology (equivalently, the presieve is covering
for the associated pretopology), the natural cone associated to `F` and the family of opens
associated to `R` is a limit cone iff the natural cone associated to `F` and the generated
sieve is a limit cone.
Since only the existence of a 1-1 correspondence will be used, the exact definition does
not matter, so tactics are used liberally. -/
/-
**TopCat.Presheaf.isLimitOpensLeEquivGenerate** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.
Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf `F` on the topological space `X` and a presieve `R` whose gener
ated sieve
is covering for the associated Grothendieck topology (equivalently, the presieve
 is covering
for the associated pretopology), the natural cone associated to `F` and the fami
ly of opens
associated to `R` is a limit cone iff the natural cone associated to `F` and the
 generated
sieve is a limit cone.
Since only the existence of a 1-1 correspondence will be used, the exact definit
ion does
not matter, so tactics are used liberally.
-/
def isLimitOpensLeEquivGenerate₂ (R : Presieve Y)
    (hR : Sieve.generate R ∈ Opens.grothendieckTopology X Y) :
    IsLimit (F.mapCone (opensLeCoverCocone (coveringOfPresieve Y R)).op) ≃
      IsLimit (F.mapCone (Sieve.generate R).arrows.cocone.op) := by
  convert!
    isLimitOpensLeEquivGenerate₁ F (coveringOfPresieve Y R)
      (coveringOfPresieve.iSup_eq_of_mem_grothendieck Y R hR).symm using 1
  rw [covering_presieve_eq_self R]

variable {F} in
/-
**TopCat.Presheaf.IsSheaf.isSheafOpensLeCover** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.
Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : TopCat
} {F : TopCat.Presheaf C X} {ι : Type u_2}   (U : ι → TopologicalSpace.Opens ↑X)
,   F.IsSheaf →     Nonempty       (CategoryTheory.Limits.IsLimit         (Categ
oryTheory.Functor.mapCone F (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U
).op))
参数：U : ι → TopologicalSpace.Opens ↑X；CategoryTheory.Limits.IsLimit         (Cate
goryTheory.Functor.mapCone F (TopCat.Presheaf.SheafCondition.opensLeCoverCocone 
U).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit`：isSheaf_iff_isLimit : IsShe
af J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone 
S.arrows.cocone.op))
· 使用定理 `TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology`：mem_grothen
dieckTopology : Sieve.generate (presieveOfCovering U) in Opens.grothendieckTopol
ogy X (iSup U)
-/
theorem IsSheaf.isSheafOpensLeCover (h : F.IsSheaf) :
    Nonempty (IsLimit (F.mapCone (opensLeCoverCocone U).op)) := by
  rw [(isLimitOpensLeEquivGenerate₁ F U rfl).nonempty_congr]
  apply (Presheaf.isSheaf_iff_isLimit _ _).mp h
  apply presieveOfCovering.mem_grothendieckTopology

/-- A presheaf `(opens X)ᵒᵖ ⥤ C` on a topological space `X` is a sheaf on the site `opens X` iff
it satisfies the `IsSheafOpensLeCover` sheaf condition. The latter is not the
official definition of sheaves on spaces, but has the advantage that it does not
require `has_products C`. -/
/-
**TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover** 是 Mathlib 中的一个定理，位于命名空间 `Top
Cat.Presheaf`。
形式化陈述：isSheaf_iff_isSheafOpensLeCover : F.IsSheaf ↔ F.IsSheafOpensLeCover
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.IsSheaf.isSheafOpensLeCover`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {X : TopCat} {F : TopCat.Presheaf C X} {ι : 
Type u_2}   (U : ι → TopologicalS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit`：isSheaf_iff_isLimit : IsShe
af J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone 
S.arrows.cocone.op))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β

--- 原说明 ---
A presheaf `(opens X)ᵒᵖ ⥤ C` on a topological space `X` is a sheaf on the site `
opens X` iff
it satisfies the `IsSheafOpensLeCover` sheaf condition. The latter is not the
official definition of sheaves on spaces, but has the advantage that it does not
require `has_products C`.
-/
theorem isSheaf_iff_isSheafOpensLeCover : F.IsSheaf ↔ F.IsSheafOpensLeCover := by
  refine ⟨fun h _ ↦ h.isSheafOpensLeCover,
    fun h ↦ (Presheaf.isSheaf_iff_isLimit _ _).mpr fun Y S ↦ ?_⟩
  rw [← Sieve.generate_sieve S]
  intro hS
  rw [← (isLimitOpensLeEquivGenerate₂ F S.1 hS).nonempty_congr]
  apply h

end

end Presheaf

end TopCat

