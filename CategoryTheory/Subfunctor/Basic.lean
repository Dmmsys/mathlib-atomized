/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Set.Lattice.Image

/-!

# Subfunctor of types

We define subfunctors of a type-valued functors.

## Main definition

`CategoryTheory.Subfunctor` : A subfunctor of a type-valued functor.

-/

@[expose] public section


universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A subfunctor of a functor consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
/--
Definition of `Subfunctor` / `Subfunctor` 的定义

English:
structure Subfunctor
  parameters: (F : C ⥤ Type w)
  axioms and operations (2):
    - obj : forall U, Set (F.obj U)
    - map : forall {U V : C} (i : U ⟶ V), obj U subseteq F.map i ⁻¹' obj V

中文:
结构 子函子
  参数: (F : C ⥤ 类型 w)
  公理与运算 (2 个):
    - obj : 对任意 U, 集合 (F.obj U)
    - map : 对任意 {U V : C} (i : U ⟶ V), obj U subseteq F.map i ⁻¹' obj V
-/
structure Subfunctor (F : C ⥤ Type w) where
  /-- If `G` is a subfunctor of `F`, then the sections of `G` on `U` forms a subset of sections of
  `F` on `U`. -/
  obj : forall U, Set (F.obj U)
  /-- If `G` is a subfunctor of `F` and `i : U ⟶ V`, then for each `G`-sections on `U` `x`,
  `F i x` is in `F(V)`. -/
  map : forall {U V : C} (i : U ⟶ V), obj U subseteq F.map i ⁻¹' obj V

variable {F F' F'' : C ⥤ Type w} (G G' : Subfunctor F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subfunctor F)
  body: PartialOrder.lift Subfunctor.obj (fun _ _ => Subfunctor.ext)

中文:
实例 :
  签名: 偏序 (子函子 F)
  定义体: PartialOrder.lift Subfunctor.obj (fun _ _ => Subfunctor.ext)

Depends on / 依赖: PartialOrder, PartialOrder.lift, Subfunctor, Subfunctor.ext, Subfunctor.obj
-/
instance : PartialOrder (Subfunctor F) :=
  PartialOrder.lift Subfunctor.obj (fun _ _ => Subfunctor.ext)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subfunctor F)
  body: { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h | h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h | h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf

中文:
实例 :
  签名: 完备格 (子函子 F)
  定义体: { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h | h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h | h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf

Depends on / 依赖: F.map, F.obj, G.map, G.obj, Or.inl, Or.inr, S.map, S.obj, Set.image, T.map, T.obj, inf_le_left, inf_le_right, le_inf, le_sup_left, le_sup_right, sup_le
-/
instance : CompleteLattice (Subfunctor F) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h | h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h | h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T => T.obj U) S)
      map f x hx := by
        obtain ⟨_, ⟨F, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, F.map f h'⟩ }
  isLUB_sSup _ := ⟨fun _ _ _ _ => by aesop, fun _ _ _ => by aesop⟩
  sInf S :=
    { obj U := sInf (Set.image (fun T => T.obj U) S)
      map f x hx := by
        rintro _ ⟨F, h, rfl⟩
        exact F.map f (hx _ ⟨_, h, rfl⟩) }
  isGLB_sInf _ := ⟨fun _ _ _ _ => by aesop, fun _ _ _ => by aesop⟩
  bot :=
    { obj U := ⊥
      map := by simp }
  bot_le _ _ := bot_le
  top :=
    { obj U := ⊤
      map := by simp }
  le_top _ _ := le_top

namespace Subfunctor

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: (S T : Subfunctor F)
  statement: S <= T ↔ forall U, S.obj U <= T.obj U
  proof: Iff.rfl

中文:
引理 le_def
  条件: (S T : 子函子 F)
  结论: S <= T ↔ 对任意 U, S.obj U <= T.obj U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def (S T : Subfunctor F) : S <= T ↔ forall U, S.obj U <= T.obj U := Iff.rfl

variable (F)

/--
lemma `top_obj` / 引理 `top_obj`

English:
lemma top_obj
  given: (i : C)
  statement: (⊤ : Subfunctor F).obj i = ⊤
  proof: rfl

中文:
引理 top_obj
  条件: (i : C)
  结论: (⊤ : 子函子 F).obj i = ⊤
  证明: rfl
-/
@[simp] lemma top_obj (i : C) : (⊤ : Subfunctor F).obj i = ⊤ := rfl
/--
lemma `bot_obj` / 引理 `bot_obj`

English:
lemma bot_obj
  given: (i : C)
  statement: (⊥ : Subfunctor F).obj i = ⊥
  proof: rfl

中文:
引理 bot_obj
  条件: (i : C)
  结论: (⊥ : 子函子 F).obj i = ⊥
  证明: rfl
-/
@[simp] lemma bot_obj (i : C) : (⊥ : Subfunctor F).obj i = ⊥ := rfl

variable {F}

/--
lemma `sSup_obj` / 引理 `sSup_obj`

English:
lemma sSup_obj
  given: (S : Set (Subfunctor F)) (U : C)
  proof: rfl

中文:
引理 sSup_obj
  条件: (S : 集合 (子函子 F)) (U : C)
  证明: rfl
-/
lemma sSup_obj (S : Set (Subfunctor F)) (U : C) :
    (sSup S).obj U = sSup (Set.image (fun T => T.obj U) S) := rfl

/--
lemma `sInf_obj` / 引理 `sInf_obj`

English:
lemma sInf_obj
  given: (S : Set (Subfunctor F)) (U : C)
  proof: rfl

@[simp]

中文:
引理 sInf_obj
  条件: (S : 集合 (子函子 F)) (U : C)
  证明: rfl

@[simp]
-/
lemma sInf_obj (S : Set (Subfunctor F)) (U : C) :
    (sInf S).obj U = sInf (Set.image (fun T => T.obj U) S) := rfl

@[simp]
/--
lemma `iSup_obj` / 引理 `iSup_obj`

English:
lemma iSup_obj
  given: {ι : Sort*} (S : ι -> Subfunctor F) (U : C)
  proof: by
  simp [iSup, sSup_obj]

@[simp]

中文:
引理 iSup_obj
  条件: {ι : 类型层*} (S : ι -> 子函子 F) (U : C)
  证明: by
  simp [iSup, sSup_obj]

@[simp]

Depends on / 依赖: sSup_obj
-/
lemma iSup_obj {ι : Sort*} (S : ι -> Subfunctor F) (U : C) :
    (⨆ i, S i).obj U = ⋃ i, (S i).obj U := by
  simp [iSup, sSup_obj]

@[simp]
/--
lemma `iInf_obj` / 引理 `iInf_obj`

English:
lemma iInf_obj
  given: {ι : Sort*} (S : ι -> Subfunctor F) (U : C)
  proof: by
  simp [iInf, sInf_obj]

@[simp]

中文:
引理 iInf_obj
  条件: {ι : 类型层*} (S : ι -> 子函子 F) (U : C)
  证明: by
  simp [iInf, sInf_obj]

@[simp]

Depends on / 依赖: sInf_obj
-/
lemma iInf_obj {ι : Sort*} (S : ι -> Subfunctor F) (U : C) :
    (⨅ i, S i).obj U = ⋂ i, (S i).obj U := by
  simp [iInf, sInf_obj]

@[simp]
/--
lemma `max_obj` / 引理 `max_obj`

English:
lemma max_obj
  given: (S T : Subfunctor F) (i : C)
  proof: rfl

@[simp]

中文:
引理 max_obj
  条件: (S T : 子函子 F) (i : C)
  证明: rfl

@[simp]
-/
lemma max_obj (S T : Subfunctor F) (i : C) :
    (S ⊔ T).obj i = S.obj i union T.obj i := rfl

@[simp]
/--
lemma `min_obj` / 引理 `min_obj`

English:
lemma min_obj
  given: (S T : Subfunctor F) (i : C)
  proof: rfl

中文:
引理 min_obj
  条件: (S T : 子函子 F) (i : C)
  证明: rfl
-/
lemma min_obj (S T : Subfunctor F) (i : C) :
    (S ⊓ T).obj i = S.obj i inter T.obj i := rfl

/--
lemma `max_min` / 引理 `max_min`

English:
lemma max_min
  given: (S₁ S₂ T : Subfunctor F)
  proof: by
  aesop

中文:
引理 max_min
  条件: (S₁ S₂ T : 子函子 F)
  证明: by
  aesop
-/
lemma max_min (S₁ S₂ T : Subfunctor F) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop

/--
lemma `iSup_min` / 引理 `iSup_min`

English:
lemma iSup_min
  given: {ι : Sort*} (S : ι -> Subfunctor F) (T : Subfunctor F)
  proof: by
  aesop

中文:
引理 iSup_min
  条件: {ι : 类型层*} (S : ι -> 子函子 F) (T : 子函子 F)
  证明: by
  aesop
-/
lemma iSup_min {ι : Sort*} (S : ι -> Subfunctor F) (T : Subfunctor F) :
    (⨆ i, S i) ⊓ T = ⨆ i, S i ⊓ T := by
  aesop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (Subfunctor F)
  body: inferInstance

中文:
实例 :
  签名: 非空 (子函子 F)
  定义体: inferInstance
-/
instance : Nonempty (Subfunctor F) :=
  inferInstance

/-- The subfunctor as a functor. -/
@[simps obj map]
/--
Definition of `toFunctor` / `toFunctor` 的定义

English:
definition toFunctor
  signature: : C ⥤ Type w where
  body: G.obj U
  map i := ↾fun x => ⟨F.map i x, G.map i x.prop⟩

中文:
定义 toFunctor
  签名: : C ⥤ 类型 w where
  定义体: G.obj U
  map i := ↾fun x => ⟨F.map i x, G.map i x.prop⟩

Depends on / 依赖: G.obj
-/
def toFunctor : C ⥤ Type w where
  obj U := G.obj U
  map i := ↾fun x => ⟨F.map i x, G.map i x.prop⟩

instance {U} : CoeHead (G.toFunctor.obj U) (F.obj U) where
  coe := Subtype.val

/-- The inclusion of a subfunctor to the original functor. -/
@[simps]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : G.toFunctor ⟶ F where app _
  body: ↾fun x => x

中文:
定义 ι
  签名: : G.toFunctor ⟶ F where app _
  定义体: ↾fun x => x
-/
def ι : G.toFunctor ⟶ F where app _ := ↾fun x => x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono G.ι
  body: ⟨@fun _ _ _ e =>
NatTrans.ext funext fun U => hom_ext _ _ fun x => Subtype.ext congr_hom (congr_app e U) x⟩

中文:
实例 :
  签名: 单态射 G.ι
  定义体: ⟨@fun _ _ _ e =>
NatTrans.ext funext fun U => hom_ext _ _ fun x => Subtype.ext congr_hom (congr_app e U) x⟩

Depends on / 依赖: NatTrans, NatTrans.ext, Subtype, Subtype.ext, congr_app, congr_hom, hom_ext
-/
instance : Mono G.ι :=
  ⟨@fun _ _ _ e =>
NatTrans.ext funext fun U => hom_ext _ _ fun x => Subtype.ext congr_hom (congr_app e U) x⟩

/-- The inclusion of a subfunctor to a larger subfunctor -/
@[simps]
/--
Definition of `homOfLe` / `homOfLe` 的定义

English:
definition homOfLe
  signature: {G G' : Subfunctor F} (h : G <= G')
  body: ↾fun x => ⟨x, h U x.prop⟩

中文:
定义 homOfLe
  签名: {G G' : 子函子 F} (h : G <= G')
  定义体: ↾fun x => ⟨x, h U x.prop⟩

Depends on / 依赖: x.prop
-/
def homOfLe {G G' : Subfunctor F} (h : G <= G') : G.toFunctor ⟶ G'.toFunctor where
  app U := ↾fun x => ⟨x, h U x.prop⟩

instance {G G' : Subfunctor F} (h : G <= G') : Mono (Subfunctor.homOfLe h) :=
⟨fun _ _ e => NatTrans.ext funext fun U => hom_ext _ _ fun x => by
    exact Subtype.ext (congr_arg Subtype.val <| (congr_hom (congr_app e U) x) :)⟩

@[reassoc (attr := simp)]
/--
theorem `homOfLe_ι` / 定理 `homOfLe_ι`

English:
theorem homOfLe_ι
  given: {G G' : Subfunctor F} (h : G <= G')
  proof: by
  ext
  rfl

中文:
定理 homOfLe_ι
  条件: {G G' : 子函子 F} (h : G <= G')
  证明: by
  ext
  rfl
-/
theorem homOfLe_ι {G G' : Subfunctor F} (h : G <= G') :
    Subfunctor.homOfLe h ≫ G'.ι = G.ι := by
  ext
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (Subfunctor.ι (⊤ : Subfunctor F))
  body: by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

中文:
实例 :
  签名: 是同构 (子函子.ι (⊤ : 子函子 F))
  定义体: by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, Subtype, Subtype.coe_injective, _root_, _root_.trivial, coe_injective, isIso_iff_bijective, isIso_of_isIso_app
-/
instance : IsIso (Subfunctor.ι (⊤ : Subfunctor F)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

/--
theorem `eq_top_iff_isIso` / 定理 `eq_top_iff_isIso`

English:
theorem eq_top_iff_isIso
  statement: G = ⊤ ↔ IsIso G.ι
  proof: by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2

中文:
定理 eq_top_iff_isIso
  结论: G = ⊤ ↔ 是同构 G.ι
  证明: by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2

Depends on / 依赖: IsIso.inv_hom_id_apply, iff_of_eq, iff_true, infer_instance, inv_hom_id_apply
-/
theorem eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι := by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2

/--
theorem `nat_trans_naturality` / 定理 `nat_trans_naturality`

English:
theorem nat_trans_naturality
  statement: (f : F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V)
  proof: congrArg Subtype.val (NatTrans.naturality_apply f i x)

@[deprecated (since := "2026-02-10")] alias toFunctor_map_coe := toFunctor_map

中文:
定理 nat_trans_naturality
  结论: (f : F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V)
  证明: congrArg Subtype.val (NatTrans.naturality_apply f i x)

@[deprecated (since := "2026-02-10")] alias toFunctor_map_coe := toFunctor_map

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, Subtype, Subtype.val, naturality_apply
-/
theorem nat_trans_naturality (f : F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congrArg Subtype.val (NatTrans.naturality_apply f i x)

@[deprecated (since := "2026-02-10")] alias toFunctor_map_coe := toFunctor_map

end Subfunctor

end CategoryTheory
