/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/

@[expose] public section


universe u

namespace CategoryTheory

/--
Definition of `typesGrothendieckTopology` / `typesGrothendieckTopology` 的定义

English:
definition typesGrothendieckTopology
  signature: : GrothendieckTopology (Type u) where
  body: {S | forall x : α, S <| ↾fun _ : PUnit => x}
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit

中文:
定义 typesGrothendieckTopology
  签名: : Grothendieck拓扑 (类型u) where
  定义体: {S | forall x : α, S <| ↾fun _ : PUnit => x}
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit
-/
def typesGrothendieckTopology : GrothendieckTopology (Type u) where
  sieves α := {S | forall x : α, S <| ↾fun _ : PUnit => x}
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simps]
/--
Definition of `discreteSieve` / `discreteSieve` 的定义

English:
definition discreteSieve
  signature: (α : Type u)
  body: exists x, forall y, f y = x
downward_closed := fun ⟨x, hx⟩ g => ⟨x, fun y => hx g y⟩

中文:
定义 discreteSieve
  签名: (α : 类型u)
  定义体: exists x, forall y, f y = x
downward_closed := fun ⟨x, hx⟩ g => ⟨x, fun y => hx g y⟩
-/
def discreteSieve (α : Type u) : Sieve α where
  arrows _ f := exists x, forall y, f y = x
downward_closed := fun ⟨x, hx⟩ g => ⟨x, fun y => hx g y⟩

/--
theorem `discreteSieve_mem` / 定理 `discreteSieve_mem`

English:
theorem discreteSieve_mem
  given: (α : Type u)
  statement: discreteSieve α in typesGrothendieckTopology α
  proof: fun x => ⟨x, fun _ => rfl⟩

中文:
定理 discreteSieve_mem
  条件: (α : 类型u)
  结论: discreteSieve α in typesGrothendieckTopology α
  证明: fun x => ⟨x, fun _ => rfl⟩
-/
theorem discreteSieve_mem (α : Type u) : discreteSieve α in typesGrothendieckTopology α :=
  fun x => ⟨x, fun _ => rfl⟩

/--
Definition of `discretePresieve` / `discretePresieve` 的定义

English:
definition discretePresieve
  signature: (α : Type u)
  body: fun β _ => exists x : β, forall y : β, y = x

中文:
定义 discretePresieve
  签名: (α : 类型u)
  定义体: fun β _ => exists x : β, forall y : β, y = x
-/
def discretePresieve (α : Type u) : Presieve α :=
  fun β _ => exists x : β, forall y : β, y = x

/--
theorem `generate_discretePresieve_mem` / 定理 `generate_discretePresieve_mem`

English:
theorem generate_discretePresieve_mem
  given: (α : Type u)
  proof: fun x => ⟨PUnit, 𝟙 _, ↾fun _ => x,
    ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩, rfl⟩

中文:
定理 generate_discretePresieve_mem
  条件: (α : 类型u)
  证明: fun x => ⟨PUnit, 𝟙 _, ↾fun _ => x,
    ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩, rfl⟩

Depends on / 依赖: PUnit.unit, Subsingleton, Subsingleton.elim
-/
theorem generate_discretePresieve_mem (α : Type u) :
    Sieve.generate (discretePresieve α) in typesGrothendieckTopology α :=
  fun x => ⟨PUnit, 𝟙 _, ↾fun _ => x,
    ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩, rfl⟩

/--
theorem `Presieve.isSheaf_yoneda'` / 定理 `Presieve.isSheaf_yoneda'`

English:
theorem Presieve.isSheaf_yoneda'
  given: {α : Type u}
  proof: fun β _ hs x hx =>
  ⟨↾fun y => (x _ (hs y)).hom PUnit.unit , fun γ f h =>
    ConcreteCategory.hom_ext _ _ fun z => by
      convert!
        ConcreteCategory.congr_hom (hx (𝟙 _) (↾fun _ => z) (hs <| f z) h rfl) PUnit.unit using 1,
      fun f hf => ConcreteCategory.hom_ext _ _ fun y => by
        

中文:
定理 Presieve.isSheaf_yoneda'
  条件: {α : 类型u}
  证明: fun β _ hs x hx =>
  ⟨↾fun y => (x _ (hs y)).hom PUnit.unit , fun γ f h =>
    ConcreteCategory.hom_ext _ _ fun z => by
      convert!
        ConcreteCategory.congr_hom (hx (𝟙 _) (↾fun _ => z) (hs <| f z) h rfl) PUnit.unit using 1,
      fun f hf => ConcreteCategory.hom_ext _ _ fun y => by
        

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ext, PUnit.unit, congr_hom, convert, hom_ext
-/
theorem Presieve.isSheaf_yoneda' {α : Type u} :
    Presieve.IsSheaf typesGrothendieckTopology (yoneda.obj α) :=
  fun β _ hs x hx =>
  ⟨↾fun y => (x _ (hs y)).hom PUnit.unit , fun γ f h =>
    ConcreteCategory.hom_ext _ _ fun z => by
      convert!
        ConcreteCategory.congr_hom (hx (𝟙 _) (↾fun _ => z) (hs <| f z) h rfl) PUnit.unit using 1,
      fun f hf => ConcreteCategory.hom_ext _ _ fun y => by
        convert! ConcreteCategory.congr_hom (hf _ (hs y)) PUnit.unit⟩

/--
theorem `Presheaf.isSheaf_yoneda'` / 定理 `Presheaf.isSheaf_yoneda'`

English:
theorem Presheaf.isSheaf_yoneda'
  given: {α : Type u}
  proof: by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_yoneda'

中文:
定理 预层.isSheaf_yoneda'
  条件: {α : 类型u}
  证明: by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_yoneda'

Depends on / 依赖: Presieve, Presieve.isSheaf_yoneda, isSheaf_iff_isSheaf_of_type, isSheaf_yoneda
-/
theorem Presheaf.isSheaf_yoneda' {α : Type u} :
    Presheaf.IsSheaf typesGrothendieckTopology (yoneda.obj α) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_yoneda'

/-- The yoneda functor that sends a type to a sheaf over the category of types. -/
@[simps]
/--
Definition of `yoneda'` / `yoneda'` 的定义

English:
definition yoneda'
  signature: : Type u ⥤ Sheaf typesGrothendieckTopology (Type u) where
  body: ⟨yoneda.obj α, Presheaf.isSheaf_yoneda'⟩
  map f := ⟨yoneda.map f⟩

@[simp]

中文:
定义 yoneda'
  签名: : 类型u ⥤ 层 typesGrothendieckTopology (类型u) where
  定义体: ⟨yoneda.obj α, Presheaf.isSheaf_yoneda'⟩
  map f := ⟨yoneda.map f⟩

@[simp]

Depends on / 依赖: Presheaf, Presheaf.isSheaf_yoneda, isSheaf_yoneda, yoneda, yoneda.obj
-/
def yoneda' : Type u ⥤ Sheaf typesGrothendieckTopology (Type u) where
  obj α := ⟨yoneda.obj α, Presheaf.isSheaf_yoneda'⟩
  map f := ⟨yoneda.map f⟩

@[simp]
/--
theorem `yoneda'_comp` / 定理 `yoneda'_comp`

English:
theorem yoneda'_comp
  statement: yoneda'.{u} ⋙ sheafToPresheaf _ _ = yoneda
  proof: rfl

中文:
定理 yoneda'_comp
  结论: yoneda'.{u} ⋙ sheafToPresheaf _ _ = yoneda
  证明: rfl
-/
theorem yoneda'_comp : yoneda'.{u} ⋙ sheafToPresheaf _ _ = yoneda :=
  rfl

open Opposite

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α))
  body: ↾fun x => P.map (↾fun _ => x).op s

中文:
定义 eval
  签名: (P : 类型uᵒᵖ ⥤ 类型u) (α : 类型u) (s : P.obj (op α))
  定义体: ↾fun x => P.map (↾fun _ => x).op s

Depends on / 依赖: P.map
-/
def eval (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) :
    α ⟶ P.obj (op PUnit) :=
  ↾fun x => P.map (↾fun _ => x).op s

open Presieve

/--
Definition of `typesGlue` / `typesGlue` 的定义

English:
definition typesGlue
  signature: (S : Type uᵒᵖ ⥤ Type u)
  body: (hs.isSheafFor _ (generate_discretePresieve_mem α)).amalgamate
    (fun _ g hg => S.map (↾fun _ => PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
    (hs.isSheafFor _ (generate_discretePresieve_mem δ)).isSeparatedFor.ext fun ε g ⟨x, _⟩ => by
      have : f₁ (

中文:
定义 typesGlue
  签名: (S : 类型uᵒᵖ ⥤ 类型u)
  定义体: (hs.isSheafFor _ (generate_discretePresieve_mem α)).amalgamate
    (fun _ g hg => S.map (↾fun _ => PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
    (hs.isSheafFor _ (generate_discretePresieve_mem δ)).isSeparatedFor.ext fun ε g ⟨x, _⟩ => by
      have : f₁ (

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, ConcreteCategory, ConcreteCategory.congr_hom, Functor, Functor.map_comp, PUnit.unit, S.map, amalgamate, choose_spec, comp_apply, congr_hom, generate_discretePresieve_mem, hs.isSheafFor, isSeparatedFor, isSeparatedFor.ext, isSheafFor, map_comp, simp_rw
-/
noncomputable def typesGlue (S : Type uᵒᵖ ⥤ Type u)
    (hs : IsSheaf typesGrothendieckTopology S) (α : Type u)
    (f : α -> S.obj (op PUnit)) : S.obj (op α) :=
  (hs.isSheafFor _ (generate_discretePresieve_mem α)).amalgamate
    (fun _ g hg => S.map (↾fun _ => PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
    (hs.isSheafFor _ (generate_discretePresieve_mem δ)).isSeparatedFor.ext fun ε g ⟨x, _⟩ => by
      have : f₁ (Classical.choose hf₁) = f₂ (Classical.choose hf₂) :=
        Classical.choose_spec hf₁ (g₁ <| g x) ▸
          Classical.choose_spec hf₂ (g₂ <| g x) ▸ ConcreteCategory.congr_hom h _
      simp_rw [← comp_apply, ← Functor.map_comp, this, ← op_comp]
      rfl

/--
theorem `eval_typesGlue` / 定理 `eval_typesGlue`

English:
theorem eval_typesGlue
  given: {S hs α} (f)
  statement: eval.{u} S α (typesGlue S hs α f) = f
  proof: by
  funext x
  apply (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩).trans
  convert! ConcreteCategory.congr_hom (S.map_id _) _

中文:
定理 eval_typesGlue
  条件: {S hs α} (f)
  结论: eval.{u} S α (typesGlue S hs α f) = f
  证明: by
  funext x
  apply (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩).trans
  convert! ConcreteCategory.congr_hom (S.map_id _) _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, IsSheafFor, IsSheafFor.valid_glue, PUnit.unit, S.map_id, Subsingleton, Subsingleton.elim, congr_hom, convert, map_id, valid_glue
-/
theorem eval_typesGlue {S hs α} (f) : eval.{u} S α (typesGlue S hs α f) = f := by
  funext x
  apply (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩).trans
  convert! ConcreteCategory.congr_hom (S.map_id _) _

/--
theorem `typesGlue_eval` / 定理 `typesGlue_eval`

English:
theorem typesGlue_eval
  given: {S hs α} (s)
  statement: typesGlue.{u} S hs α (eval S α s) = s
  proof: by
  apply (hs.isSheafFor _ (generate_discretePresieve_mem α)).isSeparatedFor.ext
  intro β f hf
  apply (IsSheafFor.valid_glue _ _ _ hf).trans
  simp only [eval, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← comp_apply,
    ← Functor.map_comp, ← op_comp]
  congr
  ext x
  exact congr_arg f (Cla

中文:
定理 typesGlue_eval
  条件: {S hs α} (s)
  结论: typesGlue.{u} S hs α (eval S α s) = s
  证明: by
  apply (hs.isSheafFor _ (generate_discretePresieve_mem α)).isSeparatedFor.ext
  intro β f hf
  apply (IsSheafFor.valid_glue _ _ _ hf).trans
  simp only [eval, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← comp_apply,
    ← Functor.map_comp, ← op_comp]
  congr
  ext x
  exact congr_arg f (Cla

Depends on / 依赖: Classical, Classical.choose_spec, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.map_comp, IsSheafFor, IsSheafFor.valid_glue, TypeCat, TypeCat.Fun.coe_mk, choose_spec, coe_mk, comp_apply, congr_arg, generate_discretePresieve_mem, hom_ofHom, hs.isSheafFor, isSeparatedFor, isSeparatedFor.ext, isSheafFor
-/
theorem typesGlue_eval {S hs α} (s) : typesGlue.{u} S hs α (eval S α s) = s := by
  apply (hs.isSheafFor _ (generate_discretePresieve_mem α)).isSeparatedFor.ext
  intro β f hf
  apply (IsSheafFor.valid_glue _ _ _ hf).trans
  simp only [eval, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← comp_apply,
    ← Functor.map_comp, ← op_comp]
  congr
  ext x
  exact congr_arg f (Classical.choose_spec hf x).symm

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
@[simps]
/--
Definition of `evalEquiv` / `evalEquiv` 的定义

English:
definition evalEquiv
  signature: (S : Type uᵒᵖ ⥤ Type u)
  body: eval S α
  invFun f := typesGlue S ((isSheaf_iff_isSheaf_of_type _ _).1 hs) α f
  left_inv := typesGlue_eval
  right_inv _ := by ext; simp [eval_typesGlue]

中文:
定义 evalEquiv
  签名: (S : 类型uᵒᵖ ⥤ 类型u)
  定义体: eval S α
  invFun f := typesGlue S ((isSheaf_iff_isSheaf_of_type _ _).1 hs) α f
  left_inv := typesGlue_eval
  right_inv _ := by ext; simp [eval_typesGlue]
-/
noncomputable def evalEquiv (S : Type uᵒᵖ ⥤ Type u)
    (hs : Presheaf.IsSheaf typesGrothendieckTopology S)
    (α : Type u) : S.obj (op α) ≃ (α ⟶ S.obj (op (PUnit))) where
  toFun := eval S α
  invFun f := typesGlue S ((isSheaf_iff_isSheaf_of_type _ _).1 hs) α f
  left_inv := typesGlue_eval
  right_inv _ := by ext; simp [eval_typesGlue]

/--
theorem `eval_map` / 定理 `eval_map`

English:
theorem eval_map
  given: (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x)
  proof: by
  simp_rw [eval, ← comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

中文:
定理 eval_map
  条件: (S : 类型uᵒᵖ ⥤ 类型u) (α β) (f : β ⟶ α) (s x)
  证明: by
  simp_rw [eval, ← comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

Depends on / 依赖: Functor, Functor.map_comp, comp_apply, map_comp, op_comp, simp_rw
-/
theorem eval_map (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) :
    eval S β (S.map f.op s) x = eval S α s (f x) := by
  simp_rw [eval, ← comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps!]
/--
Definition of `equivYoneda` / `equivYoneda` 的定义

English:
definition equivYoneda
  signature: (S : Type uᵒᵖ ⥤ Type u)
  body: NatIso.ofComponents
    (fun α => (evalEquiv S hs <| unop α).toIso) fun {α β} f => by
      dsimp
      ext
      exact eval_map S (unop α) (unop β) f.unop _ _

中文:
定义 equivYoneda
  签名: (S : 类型uᵒᵖ ⥤ 类型u)
  定义体: NatIso.ofComponents
    (fun α => (evalEquiv S hs <| unop α).toIso) fun {α β} f => by
      dsimp
      ext
      exact eval_map S (unop α) (unop β) f.unop _ _

Depends on / 依赖: NatIso, NatIso.ofComponents, evalEquiv, eval_map, f.unop, ofComponents
-/
noncomputable def equivYoneda (S : Type uᵒᵖ ⥤ Type u)
    (hs : Presheaf.IsSheaf typesGrothendieckTopology S) :
    S ≅ yoneda.obj (S.obj (op (PUnit))) :=
  NatIso.ofComponents
    (fun α => (evalEquiv S hs <| unop α).toIso) fun {α β} f => by
      dsimp
      ext
      exact eval_map S (unop α) (unop β) f.unop _ _

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
/--
Definition of `equivYoneda'` / `equivYoneda'` 的定义

English:
definition equivYoneda'
  signature: (S : Sheaf typesGrothendieckTopology (Type u))
  body: ⟨(equivYoneda S.1 S.2).hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id := by ext1; apply (equivYoneda S.1 S.2).hom_inv_id
  inv_hom_id := by ext1; apply (equivYoneda S.1 S.2).inv_hom_id

中文:
定义 equivYoneda'
  签名: (S : 层 typesGrothendieckTopology (类型u))
  定义体: ⟨(equivYoneda S.1 S.2).hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id := by ext1; apply (equivYoneda S.1 S.2).hom_inv_id
  inv_hom_id := by ext1; apply (equivYoneda S.1 S.2).inv_hom_id

Depends on / 依赖: equivYoneda
-/
noncomputable def equivYoneda' (S : Sheaf typesGrothendieckTopology (Type u)) :
    S ≅ yoneda'.obj (S.1.obj (op (PUnit))) where
  hom := ⟨(equivYoneda S.1 S.2).hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id := by ext1; apply (equivYoneda S.1 S.2).hom_inv_id
  inv_hom_id := by ext1; apply (equivYoneda S.1 S.2).inv_hom_id

/--
theorem `eval_app` / 定理 `eval_app`

English:
theorem eval_app
  statement: (S₁ S₂ : Sheaf typesGrothendieckTopology (Type u)) (f : S₁ ⟶ S₂)
  proof: (ConcreteCategory.congr_hom (f.hom.naturality (↾fun _ => x).op) s).symm

中文:
定理 eval_app
  结论: (S₁ S₂ : 层 typesGrothendieckTopology (类型u)) (f : S₁ ⟶ S₂)
  证明: (ConcreteCategory.congr_hom (f.hom.naturality (↾fun _ => x).op) s).symm

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, f.hom.naturality, naturality
-/
theorem eval_app (S₁ S₂ : Sheaf typesGrothendieckTopology (Type u)) (f : S₁ ⟶ S₂)
    (α : Type u) (s : S₁.1.obj (op α)) (x : α) :
    eval S₂.1 α (f.hom.app (op α) s) x = f.hom.app (op PUnit) (eval S₁.1 α s x) :=
  (ConcreteCategory.congr_hom (f.hom.naturality (↾fun _ => x).op) s).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `yoneda'` induces an equivalence of categories between `Type u` and
`Sheaf typesGrothendieckTopology (Type u)`. -/
@[simps!]
/--
Definition of `typeEquiv` / `typeEquiv` 的定义

English:
definition typeEquiv
  signature: : Type u ≌ Sheaf typesGrothendieckTopology (Type u) where
  body: yoneda'
  inverse := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (PUnit))
  unitIso := dsimp% NatIso.ofComponents
      (fun _α => -- α ≅ PUnit ⟶ α
        { hom := ↾fun x => ↾fun _ => x
          inv := ↾fun f => f.hom PUnit.unit })
      fun _ => rfl
counitIso := Iso.symm
      NatIso.ofCompone

中文:
定义 typeEquiv
  签名: : 类型u ≌ 层 typesGrothendieckTopology (类型u) where
  定义体: yoneda'
  inverse := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (PUnit))
  unitIso := dsimp% NatIso.ofComponents
      (fun _α => -- α ≅ PUnit ⟶ α
        { hom := ↾fun x => ↾fun _ => x
          inv := ↾fun f => f.hom PUnit.unit })
      fun _ => rfl
counitIso := Iso.symm
      NatIso.ofCompone

Depends on / 依赖: yoneda
-/
noncomputable def typeEquiv : Type u ≌ Sheaf typesGrothendieckTopology (Type u) where
  functor := yoneda'
  inverse := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (PUnit))
  unitIso := dsimp% NatIso.ofComponents
      (fun _α => -- α ≅ PUnit ⟶ α
        { hom := ↾fun x => ↾fun _ => x
          inv := ↾fun f => f.hom PUnit.unit })
      fun _ => rfl
counitIso := Iso.symm
      NatIso.ofComponents (fun S => equivYoneda' S) (fun {S₁ S₂} f => by
        ext ⟨α⟩ s
        dsimp at s ⊢
        ext x
        exact eval_app S₁ S₂ f α s x)
  functor_unitIso_comp X := by
    ext1
    apply yonedaEquiv.injective
    dsimp [yoneda', yonedaEquiv, equivYoneda, evalEquiv]
    simpa using! typesGlue_eval (S := yoneda.obj X) (𝟙 X)

/--
Instance `subcanonical_typesGrothendieckTopology` / 实例 `subcanonical_typesGrothendieckTopology`

English:
instance subcanonical_typesGrothendieckTopology
  signature: : typesGrothendieckTopology.{u}.Subcanonical
  body: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun _ => Presieve.isSheaf_yoneda'

中文:
实例 subcanonical_typesGrothendieckTopology
  签名: : typesGrothendieckTopology.{u}.子典范
  定义体: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun _ => Presieve.isSheaf_yoneda'

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj, Presieve, Presieve.isSheaf_yoneda, Subcanonical, isSheaf_yoneda, of_isSheaf_yoneda_obj
-/
instance subcanonical_typesGrothendieckTopology : typesGrothendieckTopology.{u}.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun _ => Presieve.isSheaf_yoneda'

set_option backward.defeqAttrib.useBackward true in
/--
theorem `typesGrothendieckTopology_eq_canonical` / 定理 `typesGrothendieckTopology_eq_canonical`

English:
theorem typesGrothendieckTopology_eq_canonical
  proof: by
  refine le_antisymm typesGrothendieckTopology.le_canonical (sInf_le ?_)
  refine ⟨yoneda.obj (ULift Bool), ⟨_, rfl⟩, GrothendieckTopology.ext ?_⟩
  funext α
  ext S
  refine ⟨fun hs x => ?_, fun hs β f => Presieve.isSheaf_yoneda' _ fun y => hs (f y)⟩
  by_contra hsx
  have : (↾fun _ => ULift.up 

中文:
定理 typesGrothendieckTopology_eq_canonical
  证明: by
  refine le_antisymm typesGrothendieckTopology.le_canonical (sInf_le ?_)
  refine ⟨yoneda.obj (ULift Bool), ⟨_, rfl⟩, GrothendieckTopology.ext ?_⟩
  funext α
  ext S
  refine ⟨fun hs x => ?_, fun hs β f => Presieve.isSheaf_yoneda' _ fun y => hs (f y)⟩
  by_contra hsx
  have : (↾fun _ => ULift.up 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext_iff, GrothendieckTopology, GrothendieckTopology.ext, Presieve, Presieve.isSheaf_yoneda, ULift.up, hom_ext_iff, hsx.elim, isSeparatedFor, isSeparatedFor.ext, isSheaf_yoneda, le_antisymm, le_canonical, sInf_le, typesGrothendieckTopology, typesGrothendieckTopology.le_canonical, yoneda, yoneda.obj
-/
theorem typesGrothendieckTopology_eq_canonical :
    typesGrothendieckTopology.{u} = Sheaf.canonicalTopology (Type u) := by
  refine le_antisymm typesGrothendieckTopology.le_canonical (sInf_le ?_)
  refine ⟨yoneda.obj (ULift Bool), ⟨_, rfl⟩, GrothendieckTopology.ext ?_⟩
  funext α
  ext S
  refine ⟨fun hs x => ?_, fun hs β f => Presieve.isSheaf_yoneda' _ fun y => hs (f y)⟩
  by_contra hsx
  have : (↾fun _ => ULift.up true) = ↾fun _ => ULift.up false :=
    (hs PUnit (↾fun _ => x)).isSeparatedFor.ext
      fun β f hf => by
        dsimp
        ext y
exact hsx.elim S.2 hf (↾fun _ => y)
  simp [ConcreteCategory.hom_ext_iff] at this


end CategoryTheory
