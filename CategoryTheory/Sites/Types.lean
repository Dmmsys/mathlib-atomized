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

/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
/-
**CategoryTheory.typesGrothendieckTopology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：typesGrothendieckTopology : GrothendieckTopology (Type u) where sieves α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective.
-/
def typesGrothendieckTopology : GrothendieckTopology (Type u) where
  sieves α := {S | ∀ x : α, S <| ↾fun _ : PUnit => x}
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simps]
/-
**CategoryTheory.discreteSieve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：discreteSieve (α : Type u) : Sieve α where arrows _ f
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete sieve on a type, which only includes arrows whose image is a subsin
gleton.
-/
def discreteSieve (α : Type u) : Sieve α where
  arrows _ f := ∃ x, ∀ y, f y = x
  downward_closed := fun ⟨x, hx⟩ g => ⟨x, fun y => hx <| g y⟩
/-
**CategoryTheory.discreteSieve_mem** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：discreteSieve_mem (α : Type u) : discreteSieve α in typesGrothendieckTopol
ogy α
参数：α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem discreteSieve_mem (α : Type u) : discreteSieve α ∈ typesGrothendieckTopology α :=
  fun x => ⟨x, fun _ => rfl⟩

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
/-
**CategoryTheory.discretePresieve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：discretePresieve (α : Type u) : Presieve α
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete presieve on a type, which only includes arrows whose domain is a si
ngleton.
-/
def discretePresieve (α : Type u) : Presieve α :=
  fun β _ => ∃ x : β, ∀ y : β, y = x
/-
**CategoryTheory.generate_discretePresieve_mem** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：generate_discretePresieve_mem (α : Type u) : Sieve.generate (discretePresi
eve α) in typesGrothendieckTopology α
参数：α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem generate_discretePresieve_mem (α : Type u) :
    Sieve.generate (discretePresieve α) ∈ typesGrothendieckTopology α :=
  fun x => ⟨PUnit, 𝟙 _, ↾fun _ => x,
    ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩, rfl⟩

/-- The sheaf condition for `yoneda'`. -/
/-
**CategoryTheory.Presieve.isSheaf_yoneda'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：∀ {α : Type u}, CategoryTheory.Presieve.IsSheaf CategoryTheory.typesGrothe
ndieckTopology (CategoryTheory.yoneda.obj α)
参数：CategoryTheory.yoneda.obj α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x

--- 原说明 ---
The sheaf condition for `yoneda'`.
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

/-- The sheaf condition for `yoneda'`. -/
/-
**CategoryTheory.Presheaf.isSheaf_yoneda'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presheaf`。
形式化陈述：∀ {α : Type u}, CategoryTheory.Presheaf.IsSheaf CategoryTheory.typesGrothe
ndieckTopology (CategoryTheory.yoneda.obj α)
参数：CategoryTheory.yoneda.obj α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Presieve.isSheaf_yoneda'`：∀ {α : Type u}, CategoryTheory.
Presieve.IsSheaf CategoryTheory.typesGrothendieckTopology (CategoryTheory.yoneda
.obj α)

--- 原说明 ---
The sheaf condition for `yoneda'`.
-/
theorem Presheaf.isSheaf_yoneda' {α : Type u} :
    Presheaf.IsSheaf typesGrothendieckTopology (yoneda.obj α) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_yoneda'

/-- The yoneda functor that sends a type to a sheaf over the category of types. -/
@[simps]
/-
**CategoryTheory.yoneda'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yoneda' : Type u ⥤ Sheaf typesGrothendieckTopology (Type u) where obj α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_yoneda'`：∀ {α : Type u}, CategoryTheory.
Presheaf.IsSheaf CategoryTheory.typesGrothendieckTopology (CategoryTheory.yoneda
.obj α)

--- 原说明 ---
The yoneda functor that sends a type to a sheaf over the category of types.
-/
def yoneda' : Type u ⥤ Sheaf typesGrothendieckTopology (Type u) where
  obj α := ⟨yoneda.obj α, Presheaf.isSheaf_yoneda'⟩
  map f := ⟨yoneda.map f⟩

@[simp]
/-
**CategoryTheory.yoneda'_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：CategoryTheory.yoneda'.comp (CategoryTheory.sheafToPresheaf CategoryTheory
.typesGrothendieckTopology (Type u)) =   CategoryTheory.yoneda
参数：CategoryTheory.sheafToPresheaf CategoryTheory.typesGrothendieckTopology (Type
 u)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yoneda'_comp : yoneda'.{u} ⋙ sheafToPresheaf _ _ = yoneda :=
  rfl

open Opposite

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
/-
**CategoryTheory.eval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eval (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) : α ⟶ P.obj (
op PUnit)
参数：P : Type uᵒᵖ ⥤ Type u；α : Type u；s : P.obj (op α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`.
-/
def eval (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) :
    α ⟶ P.obj (op PUnit) :=
  ↾fun x ↦ P.map (↾fun _ => x).op s

open Presieve

/-- Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`. -/
/-
**CategoryTheory.typesGlue** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：typesGlue (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology 
S) (α : Type u) (f : α -> S.obj (op PUnit)) : S.obj (op α)
参数：S : Type uᵒᵖ ⥤ Type u；hs : IsSheaf typesGrothendieckTopology S；α : Type u；f :
 α -> S.obj (op PUnit)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`.
-/
noncomputable def typesGlue (S : Type uᵒᵖ ⥤ Type u)
    (hs : IsSheaf typesGrothendieckTopology S) (α : Type u)
    (f : α → S.obj (op PUnit)) : S.obj (op α) :=
  (hs.isSheafFor _ (generate_discretePresieve_mem α)).amalgamate
    (fun _ g hg => S.map (↾fun _ => PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
    (hs.isSheafFor _ (generate_discretePresieve_mem δ)).isSeparatedFor.ext fun ε g ⟨x, _⟩ => by
      have : f₁ (Classical.choose hf₁) = f₂ (Classical.choose hf₂) :=
        Classical.choose_spec hf₁ (g₁ <| g x) ▸
          Classical.choose_spec hf₂ (g₂ <| g x) ▸ ConcreteCategory.congr_hom h _
      simp_rw [← comp_apply, ← Functor.map_comp, this, ← op_comp]
      rfl
/-
**CategoryTheory.eval_typesGlue** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eval_typesGlue {S hs α} (f) : eval.{u} S α (typesGlue S hs α f) = f
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem eval_typesGlue {S hs α} (f) : eval.{u} S α (typesGlue S hs α f) = f := by
  funext x
  apply (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩).trans
  convert! ConcreteCategory.congr_hom (S.map_id _) _
/-
**CategoryTheory.typesGlue_eval** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：typesGlue_eval {S hs α} (s) : typesGlue.{u} S hs α (eval S α s) = s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSheafFor`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTopology C}
   {P : CategoryTheory.Functor C…
· 使用定理 `CategoryTheory.generate_discretePresieve_mem`：generate_discretePresieve_
mem (α : Type u) : Sieve.generate (discretePresieve α) in typesGrothendieckTopol
ogy α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
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
/-
**CategoryTheory.evalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：evalEquiv (S : Type uᵒᵖ ⥤ Type u) (hs : Presheaf.IsSheaf typesGrothendieck
Topology S) (α : Type u) : S.obj (op α) ≃ (α ⟶ S.obj (op (PUnit))) where toFun
参数：S : Type uᵒᵖ ⥤ Type u；hs : Presheaf.IsSheaf typesGrothendieckTopology S；α : T
ype u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`.
-/
noncomputable def evalEquiv (S : Type uᵒᵖ ⥤ Type u)
    (hs : Presheaf.IsSheaf typesGrothendieckTopology S)
    (α : Type u) : S.obj (op α) ≃ (α ⟶ S.obj (op (PUnit))) where
  toFun := eval S α
  invFun f := typesGlue S ((isSheaf_iff_isSheaf_of_type _ _).1 hs) α f
  left_inv := typesGlue_eval
  right_inv _ := by ext; simp [eval_typesGlue]
/-
**CategoryTheory.eval_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eval_map (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) : eval S β (S.map
 f.op s) x = eval S α s (f x)
参数：S : Type uᵒᵖ ⥤ Type u；α β；f : β ⟶ α；s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem eval_map (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) :
    eval S β (S.map f.op s) x = eval S α s (f x) := by
  simp_rw [eval, ← comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps!]
/-
**CategoryTheory.equivYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：equivYoneda (S : Type uᵒᵖ ⥤ Type u) (hs : Presheaf.IsSheaf typesGrothendie
ckTopology S) : S ≅ yoneda.obj (S.obj (op (PUnit)))
参数：S : Type uᵒᵖ ⥤ Type u；hs : Presheaf.IsSheaf typesGrothendieckTopology S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`.
-/
noncomputable def equivYoneda (S : Type uᵒᵖ ⥤ Type u)
    (hs : Presheaf.IsSheaf typesGrothendieckTopology S) :
    S ≅ yoneda.obj (S.obj (op (PUnit))) :=
  NatIso.ofComponents
    (fun α ↦ (evalEquiv S hs <| unop α).toIso) fun {α β} f => by
      dsimp
      ext
      exact eval_map S (unop α) (unop β) f.unop _ _

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
/-
**CategoryTheory.equivYoneda'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：equivYoneda' (S : Sheaf typesGrothendieckTopology (Type u)) : S ≅ yoneda'.
obj (S.1.obj (op (PUnit))) where hom
参数：S : Sheaf typesGrothendieckTopology (Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`.
-/
noncomputable def equivYoneda' (S : Sheaf typesGrothendieckTopology (Type u)) :
    S ≅ yoneda'.obj (S.1.obj (op (PUnit))) where
  hom := ⟨(equivYoneda S.1 S.2).hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id := by ext1; apply (equivYoneda S.1 S.2).hom_inv_id
  inv_hom_id := by ext1; apply (equivYoneda S.1 S.2).inv_hom_id
/-
**CategoryTheory.eval_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eval_app (S₁ S₂ : Sheaf typesGrothendieckTopology (Type u)) (f : S₁ ⟶ S₂) 
(α : Type u) (s : S₁.1.obj (op α)) (x : α) : eval S₂.1 α (f.hom.app (op α) s) x 
= f.hom.app (op PUnit) (eval S₁.1 α s x)
参数：S₁ S₂ : Sheaf typesGrothendieckTopology (Type u)；f : S₁ ⟶ S₂；α : Type u；s : S
₁.1.obj (op α)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
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
/-
**CategoryTheory.typeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：typeEquiv : Type u ≌ Sheaf typesGrothendieckTopology (Type u) where functo
r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`yoneda'` induces an equivalence of categories between `Type u` and
`Sheaf typesGrothendieckTopology (Type u)`.
-/
noncomputable def typeEquiv : Type u ≌ Sheaf typesGrothendieckTopology (Type u) where
  functor := yoneda'
  inverse := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (PUnit))
  unitIso := dsimp% NatIso.ofComponents
      (fun _α => -- α ≅ PUnit ⟶ α
        { hom := ↾fun x => ↾fun _ => x
          inv := ↾fun f => f.hom PUnit.unit })
      fun _ => rfl
  counitIso := Iso.symm <|
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
/-
**CategoryTheory.subcanonical_typesGrothendieckTopology** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory`。
形式化陈述：subcanonical_typesGrothendieckTopology : typesGrothendieckTopology.{u}.Sub
canonical
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用定理 `CategoryTheory.Presieve.isSheaf_yoneda'`：∀ {α : Type u}, CategoryTheory.
Presieve.IsSheaf CategoryTheory.typesGrothendieckTopology (CategoryTheory.yoneda
.obj α)
-/
instance subcanonical_typesGrothendieckTopology : typesGrothendieckTopology.{u}.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun _ => Presieve.isSheaf_yoneda'

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.typesGrothendieckTopology_eq_canonical** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：typesGrothendieckTopology_eq_canonical : typesGrothendieckTopology.{u} = S
heaf.canonicalTopology (Type u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.GrothendieckTopology.le_canonical`：le_canonical (J : Grot
hendieckTopology C) [Subcanonical J] : J <= canonicalTopology C
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Presieve.isSheaf_yoneda'`：∀ {α : Type u}, CategoryTheory.
Presieve.IsSheaf CategoryTheory.typesGrothendieckTopology (CategoryTheory.yoneda
.obj α)
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
        exact hsx.elim <| S.2 hf (↾fun _ => y)
  simp [ConcreteCategory.hom_ext_iff] at this


end CategoryTheory

