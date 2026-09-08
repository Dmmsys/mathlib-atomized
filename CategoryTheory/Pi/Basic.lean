/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]


/-- `pi C` gives the Cartesian product of an indexed family of categories.
-/
/-
**CategoryTheory.pi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：pi : Category.{max w₀ v₁} (forall i, C i) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pi C` gives the Cartesian product of an indexed family of categories.
-/
instance pi : Category.{max w₀ v₁} (∀ i, C i) where
  Hom X Y := ∀ i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i

namespace Pi

@[simp]
/-
**CategoryTheory.Pi.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：id_apply (X : forall i, C i) (i) : (𝟙 X : forall i, X i ⟶ X i) i = 𝟙 (X i)
参数：X : forall i, C i；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (X : ∀ i, C i) (i) : (𝟙 X : ∀ i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl

@[simp]
/-
**CategoryTheory.Pi.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：comp_apply {X Y Z : forall i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) : (f ≫ g : 
forall i, X i ⟶ Z i) i = f i ≫ g i
参数：f : X ⟶ Y；g : Y ⟶ Z；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
    (f ≫ g : ∀ i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl

@[ext]
/-
**CategoryTheory.Pi.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：ext {X Y : forall i, C i} {f g : X ⟶ Y} (w : forall i, f i = g i) : f = g
参数：w : forall i, f i = g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext {X Y : ∀ i, C i} {f g : X ⟶ Y} (w : ∀ i, f i = g i) : f = g :=
  funext (w ·)

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
/-
**CategoryTheory.Pi.eval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：eval (i : I) : (forall i, C i) ⥤ C i where obj f
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to t
he object over `i`.
-/
def eval (i : I) : (∀ i, C i) ⥤ C i where
  obj f := f i
  map α := α i

section

variable {J : Type w₁}

/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : J → I) : (j : J) → Category ((C ∘ f) j) :=
  inferInstanceAs <| (j : J) → Category (C (f j))

/-- Pull back an `I`-indexed family of objects to a `J`-indexed family, along a function `J → I`.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Pi.comap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：comap (h : J -> I) : (forall i, C i) ⥤ (forall j, C (h j)) where obj f i
参数：h : J -> I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back an `I`-indexed family of objects to a `J`-indexed family, along a func
tion `J → I`.
-/
def comap (h : J → I) : (∀ i, C i) ⥤ (∀ j, C (h j)) where
  obj f i := f (h i)
  map α i := α (h i)

variable (I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
/-
**CategoryTheory.Pi.comapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：comapId : comap C (id : I -> I) ≅ 𝟭 (forall i, C i) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor.
-/
def comapId : comap C (id : I → I) ≅ 𝟭 (∀ i, C i) where
  hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (g : J → I) : (j : J) → Category (C (g j)) := by infer_instance

variable {I}
variable {K : Type w₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps!]
/-
**CategoryTheory.Pi.comapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：comapComp (f : K -> J) (g : J -> I) : comap C g ⋙ comap (C ∘ g) f ≅ comap 
C (g ∘ f) where hom
参数：f : K -> J；g : J -> I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
def comapComp (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) where
  hom :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps!]
/-
**CategoryTheory.Pi.comapEvalIsoEval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
i`。
形式化陈述：comapEvalIsoEval (h : J -> I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval 
C (h j)
参数：h : J -> I；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between pulling back then evaluating, and just evaluatin
g.
-/
def comapEvalIsoEval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

end

section

variable {J : Type w₀} {D : J → Type u₁} [∀ j, Category.{v₁} (D j)]

/-
**CategoryTheory.Pi.sumElimCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi
`。
形式化陈述：{I : Type w₀} →   (C : I → Type u₁) →     [(i : I) → CategoryTheory.Catego
ry.{v₁, u₁} (C i)] →       {J : Type w₀} →         {D : J → Type u₁} →          
 [(j : J) → CategoryTheory.Category.{v₁, u₁} (D j)] →             (s : I ⊕ J) → 
CategoryTheory.Category.{v₁, u₁} (Sum.elim C D s)
参数：C : I → Type u₁；i : I；C i；j : J；D j；s : I ⊕ J；Sum.elim C D s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sumElimCategory : ∀ s : I ⊕ J, Category.{v₁} (Sum.elim C D s)
  | Sum.inl i => inferInstanceAs <| Category (C i)
  | Sum.inr j => inferInstanceAs <| Category (D j)

set_option backward.isDefEq.respectTransparency false in
/-- The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
/-
**CategoryTheory.Pi.sum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：sum : (forall i, C i) ⥤ (forall j, D j) ⥤ forall s : I oplus J, Sum.elim C
 D s where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifunctor combining an `I`-indexed family of objects with a `J`-indexed fami
ly of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
def sum : (∀ i, C i) ⥤ (∀ j, D j) ⥤ ∀ s : I ⊕ J, Sum.elim C D s where
  obj X :=
    { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {_} {_} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr j => 𝟙 (Y j) }

end

variable {C}

/-- A family of isomorphisms gives rise to an isomorphism of families. -/
@[simps]
/-
**CategoryTheory.Pi.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：isoMk {X Y : forall i, C i} (iso : forall i, X i ≅ Y i) : X ≅ Y where hom
参数：iso : forall i, X i ≅ Y i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of isomorphisms gives rise to an isomorphism of families.
-/
def isoMk {X Y : ∀ i, C i} (iso : ∀ i, X i ≅ Y i) :
    X ≅ Y where
  hom := fun i => (iso i).hom
  inv := fun i => (iso i).inv

/-- An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components. -/
@[simps]
/-
**CategoryTheory.Pi.isoApp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：isoApp {X Y : forall i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i
参数：f : X ≅ Y；i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components.
-/
def isoApp {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

@[simp]
/-
**CategoryTheory.Pi.isoApp_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：isoApp_refl (X : forall i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl
 (X i)
参数：X : forall i, C i；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_refl (X : ∀ i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl (X i) :=
  rfl

@[simp]
/-
**CategoryTheory.Pi.isoApp_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：isoApp_symm {X Y : forall i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = 
(isoApp f i).symm
参数：f : X ≅ Y；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_symm {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = (isoApp f i).symm :=
  rfl

@[simp]
/-
**CategoryTheory.Pi.isoApp_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：isoApp_trans {X Y Z : forall i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) : iso
App (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i
参数：f : X ≅ Y；g : Y ≅ Z；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_trans {X Y Z : ∀ i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) :
    isoApp (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i :=
  rfl

end Pi

namespace Functor

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] {A : Type u₃} [Category.{v₃} A]

/-- Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
/-
**CategoryTheory.Functor.pi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pi (F : forall i, C i ⥤ D i) : (forall i, C i) ⥤ forall i, D i where obj f
 i
参数：F : forall i, C i ⥤ D i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
  obj f i := (F i).obj (f i)
  map α i := (F i).map (α i)

/-- Similar to `pi`, but all functors come from the same category `A`
-/
@[simps]
/-
**CategoryTheory.Functor.pi'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pi' (f : forall i, A ⥤ C i) : A ⥤ forall i, C i where obj a i
参数：f : forall i, A ⥤ C i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Similar to `pi`, but all functors come from the same category `A`
-/
def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
  obj a i := (f i).obj a
  map h i := (f i).map h

/-- The projections of `Functor.pi' F` are isomorphic to the functors of the family `F` -/
@[simps!]
/-
**CategoryTheory.Functor.pi'CompEval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：{I : Type w₀} →   {C : I → Type u₁} →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] →       {A : Type u_1} →         [inst_1 : CategoryThe
ory.Category.{v_1, u_1} A] →           (F : (i : I) → CategoryTheory.Functor A (
C i)) →             (i : I) → (CategoryTheory.Functor.pi' F).comp (CategoryTheor
y.Pi.eval C i) ≅ F i
参数：i : I；C i；F : (i : I) → CategoryTheory.Functor A (C i)；i : I；CategoryTheory.F
unctor.pi' F；CategoryTheory.Pi.eval C i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projections of `Functor.pi' F` are isomorphic to the functors of the family 
`F`
-/
def pi'CompEval {A : Type*} [Category* A] (F : ∀ i, A ⥤ C i) (i : I) :
    pi' F ⋙ Pi.eval C i ≅ F i :=
  Iso.refl _

section EqToHom

@[simp]
/-
**CategoryTheory.Functor.eqToHom_proj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：eqToHom_proj {x x' : forall i, C i} (h : x = x') (i : I) : (eqToHom h : x 
⟶ x') i = eqToHom (funext_iff.mp h i)
参数：h : x = x'；i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem eqToHom_proj {x x' : ∀ i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

end EqToHom

-- One could add some natural isomorphisms showing
-- how `Functor.pi` commutes with `Pi.eval` and `Pi.comap`.
@[simp]
/-
**CategoryTheory.Functor.pi'_eval** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：∀ {I : Type w₀} {C : I → Type u₁} [inst : (i : I) → CategoryTheory.Categor
y.{v₁, u₁} (C i)] {A : Type u₃}   [inst_1 : CategoryTheory.Category.{v₃, u₃} A] 
(f : (i : I) → CategoryTheory.Functor A (C i)) (i : I),   (CategoryTheory.Functo
r.pi' f).comp (CategoryTheory.Pi.eval C i) = f i
参数：i : I；C i；f : (i : I) → CategoryTheory.Functor A (C i)；i : I；CategoryTheory.F
unctor.pi' f；CategoryTheory.Pi.eval C i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i :=
  rfl

/-- Two functors to a product category are equal iff they agree on every coordinate. -/
/-
**CategoryTheory.Functor.pi_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：pi_ext (f f' : A ⥤ forall i, C i) (h : forall i, f ⋙ (Pi.eval C i) = f' ⋙ 
(Pi.eval C i)) : f = f'
参数：f f' : A ⥤ forall i, C i；h : forall i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pi.eval_obj`：∀ {I : Type w₀} (C : I → Type u₁) [inst : (i
 : I) → CategoryTheory.Category.{v₁, u₁} (C i)] (i : I) (f : (i : I) → C i),   (
CategoryTheory.P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `CategoryTheory.Functor.eqToHom_proj`：eqToHom_proj {x x' : forall i, C i}
 (h : x = x') (i : I) : (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i)
· 使用定理 `CategoryTheory.Pi.eval_map`：∀ {I : Type w₀} (C : I → Type u₁) [inst : (i
 : I) → CategoryTheory.Category.{v₁, u₁} (C i)] (i : I)   {X Y : (i : I) → C i} 
(α : X ⟶ Y), (Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Two functors to a product category are equal iff they agree on every coordinate.
-/
theorem pi_ext (f f' : A ⥤ ∀ i, C i) (h : ∀ i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i)) :
    f = f' := by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    funext i
    specialize h i
    have := congr_hom h g
    simpa

end Functor

namespace NatTrans

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
variable {F G : ∀ i, C i ⥤ D i}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps!]
/-
**CategoryTheory.NatTrans.pi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTrans`
。
形式化陈述：pi (α : forall i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where app f i
参数：α : forall i, F i ⟶ G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of natural transformations into a single natural 
transformation.
-/
def pi (α : ∀ i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where
  app f i := (α i).app (f i)

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps]
/-
**CategoryTheory.NatTrans.pi'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTrans
`。
形式化陈述：pi' {E : Type*} [Category* E] {F G : E ⥤ forall i, C i} (τ : forall i, F ⋙
 Pi.eval C i ⟶ G ⋙ Pi.eval C i) : F ⟶ G where app
参数：τ : forall i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of natural transformations into a single natural 
transformation.
-/
def pi' {E : Type*} [Category* E] {F G : E ⥤ ∀ i, C i}
    (τ : ∀ i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i) : F ⟶ G where
  app := fun X i => (τ i).app X
  naturality _ _ f := by
    ext i
    exact (τ i).naturality f

end NatTrans

namespace NatIso

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
variable {F G : ∀ i, C i ⥤ D i}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
/-
**CategoryTheory.NatIso.pi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatIso`。
形式化陈述：pi (e : forall i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G where hom
参数：e : forall i, F i ≅ G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of natural isomorphisms into a single natural iso
morphism.
-/
def pi (e : ∀ i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G where
  hom := NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv)

set_option backward.isDefEq.respectTransparency false in
/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
/-
**CategoryTheory.NatIso.pi'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatIso`。
形式化陈述：pi' {E : Type*} [Category* E] {F G : E ⥤ forall i, C i} (e : forall i, F ⋙
 Pi.eval C i ≅ G ⋙ Pi.eval C i) : F ≅ G where hom
参数：e : forall i, F ⋙ Pi.eval C i ≅ G ⋙ Pi.eval C i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of natural isomorphisms into a single natural iso
morphism.
-/
def pi' {E : Type*} [Category* E] {F G : E ⥤ ∀ i, C i}
    (e : ∀ i, F ⋙ Pi.eval C i ≅ G ⋙ Pi.eval C i) : F ≅ G where
  hom := NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv)

end NatIso

variable {C}

/-
**CategoryTheory.isIso_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_pi_iff {X Y : forall i, C i} (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso
 (f i)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CategoryTheory.Pi.ext`：ext {X Y : forall i, C i} {f g : X ⟶ Y} (w : fora
ll i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
lemma isIso_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, IsIso (f i) := by
  constructor
  · intro _ i
    exact (Pi.isoApp (asIso f) i).isIso_hom
  · intro
    exact ⟨fun i => inv (f i), by cat_disch, by cat_disch⟩

variable (C)

/-- For a family of categories `C i` indexed by `I`, an equality `i = j` in `I` induces
an equivalence `C i ≌ C j`. -/
/-
**CategoryTheory.Pi.eqToEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi
`。
形式化陈述：{I : Type w₀} →   (C : I → Type u₁) → [inst : (i : I) → CategoryTheory.Cat
egory.{v₁, u₁} (C i)] → {i j : I} → i = j → (C i ≌ C j)
参数：C : I → Type u₁；i : I；C i；C i ≌ C j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a family of categories `C i` indexed by `I`, an equality `i = j` in `I` indu
ces
an equivalence `C i ≌ C j`.
-/
def Pi.eqToEquivalence {i j : I} (h : i = j) : C i ≌ C j := by subst h; rfl

/-- When `i = j`, projections `Pi.eval C i` and `Pi.eval C j` are related by the equivalence
`Pi.eqToEquivalence C h : C i ≌ C j`. -/
@[simps!]
/-
**CategoryTheory.Pi.evalCompEqToEquivalenceFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Pi`。
形式化陈述：{I : Type w₀} →   (C : I → Type u₁) →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] →       {i j : I} →         (h : i = j) →           (C
ategoryTheory.Pi.eval C i).comp (CategoryTheory.Pi.eqToEquivalence C h).functor 
≅ CategoryTheory.Pi.eval C j
参数：C : I → Type u₁；i : I；C i；h : i = j；CategoryTheory.Pi.eval C i；CategoryTheory
.Pi.eqToEquivalence C h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `i = j`, projections `Pi.eval C i` and `Pi.eval C j` are related by the equ
ivalence
`Pi.eqToEquivalence C h : C i ≌ C j`.
-/
def Pi.evalCompEqToEquivalenceFunctor {i j : I} (h : i = j) :
    Pi.eval C i ⋙ (Pi.eqToEquivalence C h).functor ≅
      Pi.eval C j :=
  eqToIso (by subst h; rfl)

/-- The equivalences given by `Pi.eqToEquivalence` are compatible with reindexing. -/
@[simps!]
/-
**CategoryTheory.Pi.eqToEquivalenceFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Pi`。
形式化陈述：{I : Type w₀} →   {J : Type w₁} →     (C : I → Type u₁) →       [inst : (i
 : I) → CategoryTheory.Category.{v₁, u₁} (C i)] →         (f : J → I) →         
  {i' j' : J} →             (h : i' = j') →               (CategoryTheory.Pi.eqT
oEquivalence C ⋯).functor ≅                 (CategoryTheory.Pi.eqToEquivalence (
fun i' => C (f i')) h).functor
参数：C : I → Type u₁；i : I；C i；f : J → I；h : i' = j'；CategoryTheory.Pi.eqToEquival
ence C ⋯；CategoryTheory.Pi.eqToEquivalence (fun i' => C (f i')) h。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The equivalences given by `Pi.eqToEquivalence` are compatible with reindexing.
-/
def Pi.eqToEquivalenceFunctorIso (f : J → I) {i' j' : J} (h : i' = j') :
    (Pi.eqToEquivalence C (congr_arg f h)).functor ≅
      (Pi.eqToEquivalence (fun i' => C (f i')) h).functor :=
  eqToIso (by subst h; rfl)

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Reindexing a family of categories gives equivalent `Pi` categories. -/
@[simps]
/-
**CategoryTheory.Pi.equivalenceOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Pi`。
形式化陈述：{I : Type w₀} →   {J : Type w₁} →     (C : I → Type u₁) →       [inst : (i
 : I) → CategoryTheory.Category.{v₁, u₁} (C i)] → (e : J ≃ I) → ((j : J) → C (e 
j)) ≌ (i : I) → C i
参数：C : I → Type u₁；i : I；C i；e : J ≃ I；(j : J) → C (e j)；i : I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Reindexing a family of categories gives equivalent `Pi` categories.
-/
noncomputable def Pi.equivalenceOfEquiv (e : J ≃ I) :
    (∀ j, C (e j)) ≌ (∀ i, C i) where
  functor := pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.eqToEquivalence C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => leftUnitor _ ≪≫
    (Pi.evalCompEqToEquivalenceFunctor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
    isoWhiskerLeft _ ((Pi.eqToEquivalenceFunctorIso C e (e.symm_apply_apply i')).symm) ≪≫
    (pi'CompEval _ _).symm ≪≫ isoWhiskerLeft _ (pi'CompEval _ _).symm ≪≫
    (associator _ _ _).symm)
  counitIso := NatIso.pi' (fun i => (associator _ _ _).symm ≪≫
    isoWhiskerRight (pi'CompEval _ _) _ ≪≫
    Pi.evalCompEqToEquivalenceFunctor C (e.apply_symm_apply i) ≪≫
    (leftUnitor _).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A product of categories indexed by `Option J` identifies to a binary product. -/
@[simps]
/-
**CategoryTheory.Pi.optionEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Pi`。
形式化陈述：{J : Type w₁} →   (C' : Option J → Type u₁) →     [inst : (i : Option J) →
 CategoryTheory.Category.{v₁, u₁} (C' i)] →       ((i : Option J) → C' i) ≌ C' n
one × ((j : J) → C' (some j))
参数：C' : Option J → Type u₁；i : Option J；C' i；(i : Option J) → C' i；(j : J) → C' 
(some j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of categories indexed by `Option J` identifies to a binary product.
-/
def Pi.optionEquivalence (C' : Option J → Type u₁) [∀ i, Category.{v₁} (C' i)] :
    (∀ i, C' i) ≌ C' none × (∀ (j : J), C' (some j)) where
  functor := Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (fun i => match i with
    | none => Prod.fst _ _
    | some i => Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := NatIso.pi' (fun i => match i with
    | none => Iso.refl _
    | some _ => Iso.refl _)
  counitIso := by exact Iso.refl _

namespace Equivalence

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble an `I`-indexed family of equivalences of categories
into a single equivalence. -/
@[simps]
/-
**CategoryTheory.Equivalence.pi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equiva
lence`。
形式化陈述：pi (E : forall i, C i ≌ D i) : (forall i, C i) ≌ (forall i, D i) where fun
ctor
参数：E : forall i, C i ≌ D i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of equivalences of categories
into a single equivalence.
-/
def pi (E : ∀ i, C i ≌ D i) : (∀ i, C i) ≌ (∀ i, D i) where
  functor := Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso)
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : ∀ i, C i ⥤ D i) [∀ i, (F i).IsEquivalence] :
    (Functor.pi F).IsEquivalence :=
  (pi (fun i => (F i).asEquivalence)).isEquivalence_functor

end Equivalence

end CategoryTheory

