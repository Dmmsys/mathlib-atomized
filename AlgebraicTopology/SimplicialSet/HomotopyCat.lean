/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.CategoryTheory.Category.ReflQuiv
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Category.Cat.Terminal

/-!

# The homotopy category of a simplicial set

The homotopy category of a simplicial set is defined as a quotient of the free category on its
underlying reflexive quiver (equivalently its one truncation). The quotient imposes an additional
hom relation on this free category, asserting that `f ≫ g = h` whenever `f`, `g`, and `h` are
respectively the 2nd, 0th, and 1st faces of a 2-simplex.

In fact, the associated functor

`SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂`

is defined by first restricting from simplicial sets to 2-truncated simplicial sets (throwing away
the data that is not used for the construction of the homotopy category) and then composing with an
analogously defined `SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u}` implemented relative to
the syntax of the 2-truncated simplex category.

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean` we show the functor
`SSet.hoFunctor` to be left adjoint to the nerve by providing an analogous decomposition of the
nerve functor, made by possible by the fact that nerves of categories are 2-coskeletal, and then
composing a pair of adjunctions, which factor through the category of 2-truncated simplicial sets.
-/

@[expose] public section

namespace SSet
open CategoryTheory Category Limits Functor Opposite Simplicial Nerve
open SimplexCategory.Truncated SimplicialObject.Truncated

universe v u

/-- A 2-truncated simplicial set `S` has an underlying refl quiver with `S _⦋0⦌₂` as its underlying
type. -/
/-
**SSet.OneTruncation** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2-truncated simplicial set `S` has an underlying refl quiver with `S _⦋0⦌₂` as
 its underlying
type.
-/
def OneTruncation₂ (S : SSet.Truncated 2) := S _⦋0⦌₂

namespace OneTruncation₂

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`. -/
@[simps -isSimp]
/-
**SSet.OneTruncation₂.reflQuiver** 是 Mathlib 中的一个实例，位于命名空间 `SSet.OneTruncation₂`
。
形式化陈述：reflQuiver (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where Ho
m
参数：S : SSet.Truncated 2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncati
on₂ S`.
-/
instance reflQuiver (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom := Truncated.Edge
  id := Truncated.Edge.id

@[ext]
/-
**SSet.OneTruncation₂.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.OneTruncation₂`。
形式化陈述：hom_ext {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y} (h :
 f.edge = g.edge) : f = g
参数：h : f.edge = g.edge。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.ext`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opposi
te.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   {x y
 : SSet.Trunc…
-/
lemma hom_ext
    {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y}
    (h : f.edge = g.edge) : f = g :=
  Truncated.Edge.ext h

set_option backward.isDefEq.respectTransparency.types false in
/-- The prefunctor on refl quivers `OneTruncation₂` induced by a morphism
of `2`-truncated simplicial sets. -/
@[simps]
/-
**SSet.OneTruncation₂.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.OneTruncation₂`。
形式化陈述：map {S T : SSet.Truncated 2} (f : S ⟶ T) : OneTruncation₂ S ⥤rq OneTruncat
ion₂ T where obj x
参数：f : S ⟶ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prefunctor on refl quivers `OneTruncation₂` induced by a morphism
of `2`-truncated simplicial sets.
-/
def map {S T : SSet.Truncated 2} (f : S ⟶ T) :
    OneTruncation₂ S ⥤rq OneTruncation₂ T where
  obj x := f.app _ x
  map e := e.map f
  map_id x := by ext; simp [← NatTrans.naturality_apply, reflQuiver_id]

end OneTruncation₂

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver. -/
@[simps]
/-
**SSet.oneTruncation** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that carries a 2-truncated simplicial set to its underlying refl qui
ver.
-/
def oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map f := OneTruncation₂.map f

namespace OneTruncation₂

@[simp]
/-
**SSet.OneTruncation₂.homOfEq_edge** 是 Mathlib 中的一个引理，位于命名空间 `SSet.OneTruncation
₂`。
形式化陈述：homOfEq_edge {X : SSet.Truncated.{u} 2} {x₁ y₁ x₂ y₂ : OneTruncation₂ X} (
f : x₁ ⟶ y₁) (hx : x₁ = x₂) (hy : y₁ = y₂) : (Quiver.homOfEq f hx hy).edge = f.e
dge
参数：f : x₁ ⟶ y₁；hx : x₁ = x₂；hy : y₁ = y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfEq_edge
    {X : SSet.Truncated.{u} 2} {x₁ y₁ x₂ y₂ : OneTruncation₂ X}
    (f : x₁ ⟶ y₁) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Quiver.homOfEq f hx hy).edge = f.edge := by
  subst hx hy
  rfl

section
variable {C : Type u} [Category.{v} C]

/-- An equivalence between the type of objects underlying a category and the type of 0-simplices in
the 2-truncated nerve. -/
@[simps! -isSimp]
/-
**SSet.OneTruncation₂.nerveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.OneTruncation₂`
。
形式化陈述：nerveEquiv : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between the type of objects underlying a category and the type of
 0-simplices in
the 2-truncated nerve.
-/
def nerveEquiv : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C :=
  CategoryTheory.nerveEquiv

/-- A hom equivalence over the function `OneTruncation₂.nerveEquiv`. -/
/-
**SSet.OneTruncation₂.nerveHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.OneTruncatio
n₂`。
形式化陈述：nerveHomEquiv {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))} :
 (X ⟶ Y) ≃ (nerveEquiv X ⟶ nerveEquiv Y)
参数：(SSet.truncation 2).obj (nerve C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hom equivalence over the function `OneTruncation₂.nerveEquiv`.
-/
def nerveHomEquiv {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))} :
    (X ⟶ Y) ≃ (nerveEquiv X ⟶ nerveEquiv Y) :=
  nerve.homEquiv
/-
**SSet.OneTruncation₂.nerveHomEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.OneTru
ncation₂`。
形式化陈述：nerveHomEquiv_apply {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve 
C))} (f : X ⟶ Y) : nerveHomEquiv f = eqToHom (congr_arg ComposableArrows.left f.
src_eq.symm) ≫ f.edge.hom ≫ eqToHom (congr_arg ComposableArrows.left f.tgt_eq)
参数：(SSet.truncation 2).obj (nerve C)；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nerveHomEquiv_apply {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
    (f : X ⟶ Y) :
    nerveHomEquiv f = eqToHom (congr_arg ComposableArrows.left f.src_eq.symm) ≫
      f.edge.hom ≫ eqToHom (congr_arg ComposableArrows.left f.tgt_eq) :=
  rfl

@[simp]
/-
**SSet.OneTruncation₂.nerveHomEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.OneTrunca
tion₂`。
形式化陈述：nerveHomEquiv_id (X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))) 
: nerveHomEquiv (𝟙rq X) = 𝟙 _
参数：X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.nerve.homEquiv_id`：homEquiv_id (x : ComposableArrows C 0)
 : homEquiv (Edge.id x) = 𝟙 _
-/
lemma nerveHomEquiv_id (X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))) :
    nerveHomEquiv (𝟙rq X) = 𝟙 _ :=
  nerve.homEquiv_id _

/-- The refl quiver underlying a nerve is isomorphic to the refl quiver underlying the category. -/
/-
**SSet.OneTruncation₂.ofNerve** 是 Mathlib 中的一个定义，位于命名空间 `SSet.OneTruncation₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The refl quiver underlying a nerve is isomorphic to the refl quiver underlying t
he category.
-/
def ofNerve₂ (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation₂ ((truncation 2).obj (nerve C))) ≅ ReflQuiv.of C :=
  ReflQuiv.isoOfEquiv.{u, u} OneTruncation₂.nerveEquiv
    (fun _ _ ↦ OneTruncation₂.nerveHomEquiv) nerveHomEquiv_id

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.OneTruncation₂.nerve_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.OneTruncatio
n₂`。
形式化陈述：nerve_hom_ext {X : (SSet.Truncated 2)} {C : Type u} [Category.{u} C] {F G 
: X ⟶ ((truncation 2).obj (nerve C))} (h : OneTruncation₂.map F = OneTruncation₂
.map G) : F = G
参数：SSet.Truncated 2；(truncation 2).obj (nerve C)；h : OneTruncation₂.map F = OneT
runcation₂.map G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.IsStrictSegal.hom_ext`：∀ {n : ℕ} {X Y : SSet.Truncated (n
 + 1)} [Y.IsStrictSegal] {f g : X ⟶ Y},   (∀ (x : X.obj (Opposite.op { obj := { 
len := 1 }, property := ⋯ …
· 使用定理 `SSet.StrictSegal.instIsStrictSegalObjTruncatedHAddNatOfNatTruncationOfIs
StrictSegal`：∀ {X : _root_.SSet} [X.IsStrictSegal] (n : ℕ), ((SSet.truncation (n
 + 1)).obj X).IsStrictSegal
· 使用引理 `SSet.Truncated.Edge.exists_of_simplex`：exists_of_simplex (s : X _⦋1⦌₂) :
 exists (x₀ x₁ : X _⦋0⦌₂) (e : Edge x₀ x₁), e.edge = s
· 使用定理 `CategoryTheory.ReflPrefunctor.congr_obj`：congr_obj {U V : Type*} [ReflQu
iver U] [ReflQuiver V] {F G : U ⥤rq V} (e : F = G) (X : U) : F.obj X = G.obj X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quiver.homOfEq.congr_simp`：∀ {V : Type u_1} [inst : Quiver V] {X Y X' Y'
 : V} (f f_1 : X ⟶ Y),   f = f_1 → ∀ (hX : X = X') (hY : Y = Y'), Quiver.homOfEq
 f hX hY = Quiv…
· 使用定理 `SSet.OneTruncation₂.map_map`：∀ {S T : SSet.Truncated 2} (f : S ⟶ T) {X Y
 : SSet.OneTruncation₂ S} (e : X ⟶ Y),   (SSet.OneTruncation₂.map f).map e = SSe
t.Truncated.Edge.…
· 使用引理 `SSet.OneTruncation₂.homOfEq_edge`：homOfEq_edge {X : SSet.Truncated.{u} 2
} {x₁ y₁ x₂ y₂ : OneTruncation₂ X} (f : x₁ ⟶ y₁) (hx : x₁ = x₂) (hy : y₁ = y₂) :
 (Quiver.homOfEq f hx …
· 使用定理 `SSet.Truncated.Edge.map_edge`：∀ {X Y : SSet.Truncated 2}   {x₀ x₁ : X.ob
j (Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 }
)}   (e : SSet.Tru…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.ReflPrefunctor.congr_hom`：congr_hom {U V : Type*} [ReflQu
iver U] [ReflQuiver V] {F G : U ⥤rq V} (e : F = G) {X Y : U} (f : X ⟶ Y) : Quive
r.homOfEq (F.map f) (congr_ob…
-/
lemma nerve_hom_ext {X : (SSet.Truncated 2)} {C : Type u} [Category.{u} C]
    {F G : X ⟶ ((truncation 2).obj (nerve C))}
    (h : OneTruncation₂.map F = OneTruncation₂.map G) : F = G :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f ↦ by
    obtain ⟨x₀, x₁, f, rfl⟩ := Truncated.Edge.exists_of_simplex f
    simpa using congr_arg Truncated.Edge.edge (ReflPrefunctor.congr_hom h f))

end
end OneTruncation₂

set_option backward.isDefEq.respectTransparency false in
/-- The refl quiver underlying a nerve is naturally isomorphic to the refl quiver underlying the
category. -/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
/-
**SSet.OneTruncation** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The refl quiver underlying a nerve is naturally isomorphic to the refl quiver un
derlying the
category.
-/
def OneTruncation₂.ofNerve₂.natIso :
    nerveFunctor₂.{u, u} ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget :=
  NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C)
    (fun F ↦ ReflPrefunctor.ext (by cat_disch) (fun x y f ↦ by
      obtain ⟨f, rfl, rfl⟩ := f
      dsimp [ofNerve₂, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso,
        Quiv.isoOfEquiv, nerveHomEquiv_apply]
      simp only [comp_id, id_comp]
      rfl))

set_option backward.privateInPublic true in
/-
**SSet.map_map_of_eq.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma map_map_of_eq.{w} {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  simp

namespace Truncated

/-- The map that picks up the initial vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
/-
**SSet.Truncated.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that picks up the initial vertex of a 2-simplex, as a morphism in the 2-
truncated
simplex category.
-/
def ι0₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

/-- The map that picks up the middle vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
/-
**SSet.Truncated.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that picks up the middle vertex of a 2-simplex, as a morphism in the 2-t
runcated
simplex category.
-/
def ι1₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

/-- The map that picks up the final vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
/-
**SSet.Truncated.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that picks up the final vertex of a 2-simplex, as a morphism in the 2-tr
uncated
simplex category.
-/
def ι2₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

/-- The initial vertex of a 2-simplex in a 2-truncated simplicial set. -/
/-
**SSet.Truncated.ev0** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial vertex of a 2-simplex in a 2-truncated simplicial set.
-/
def ev0₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι0₂.op φ

/-- The middle vertex of a 2-simplex in a 2-truncated simplicial set. -/
/-
**SSet.Truncated.ev1** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The middle vertex of a 2-simplex in a 2-truncated simplicial set.
-/
def ev1₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι1₂.op φ

/-- The final vertex of a 2-simplex in a 2-truncated simplicial set. -/
/-
**SSet.Truncated.ev2** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The final vertex of a 2-simplex in a 2-truncated simplicial set.
-/
def ev2₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι2₂.op φ

/-- The 0th face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
/-
**SSet.Truncated.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 0th face of a 2-simplex, as a morphism in the 2-truncated simplex category.
-/
def δ0₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 0

/-- The 1st face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
/-
**SSet.Truncated.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1st face of a 2-simplex, as a morphism in the 2-truncated simplex category.
-/
def δ1₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 1

/-- The 2nd face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
/-
**SSet.Truncated.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2nd face of a 2-simplex, as a morphism in the 2-truncated simplex category.
-/
def δ2₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 2

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
0th face of a 2-simplex. -/
/-
**SSet.Truncated.ev12** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set a
rising from the
0th face of a 2-simplex.
-/
def ev12₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext
      (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm),
    map_map_of_eq V rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
1st face of a 2-simplex. -/
/-
**SSet.Truncated.ev02** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set a
rising from the
1st face of a 2-simplex.
-/
def ev02₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
2nd face of a 2-simplex. -/
/-
**SSet.Truncated.ev01** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set a
rising from the
2nd face of a 2-simplex.
-/
def ev01₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext (SimplexCategory.δ_comp_δ (j := 1) le_rfl)),
    map_map_of_eq V rfl⟩

end Truncated

namespace OneTruncation₂

variable (V : SSet.Truncated.{u} 2)

/-- The 2-simplices in a 2-truncated simplicial set `V` generate a hom relation on the free
category on the underlying refl quiver of `V`. -/
/-
**SSet.OneTruncation₂.HoRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.OneTruncation₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-simplices in a 2-truncated simplicial set `V` generate a hom relation on t
he free
category on the underlying refl quiver of `V`.
-/
inductive HoRel₂ : HomRel (Cat.FreeRefl (OneTruncation₂ V)) where
  | of_compStruct {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Truncated.Edge x₀ x₁}
    {e₁₂ : Truncated.Edge x₁ x₂} {e₀₂ : Truncated.Edge x₀ x₂}
    (h : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    HoRel₂
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map
        (Quiver.Hom.toPath e₀₁ ≫ Quiver.Hom.toPath e₁₂))
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (Quiver.Hom.toPath e₀₂))

end OneTruncation₂

namespace Truncated

variable (V W : SSet.Truncated.{u} 2)

/-- The type underlying the homotopy category of a 2-truncated simplicial set `V`. -/
/-
**SSet.Truncated.HomotopyCategory** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：HomotopyCategory : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type underlying the homotopy category of a 2-truncated simplicial set `V`.
-/
def HomotopyCategory : Type u :=
  Quotient (OneTruncation₂.HoRel₂ V)
  deriving Category.{u}

namespace HomotopyCategory

/-- A canonical functor from the free category on the refl quiver underlying a 2-truncated
simplicial set `V` to its homotopy category. -/
/-
**SSet.Truncated.HomotopyCategory.quotientFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSe
t.Truncated.HomotopyCategory`。
形式化陈述：quotientFunctor : Cat.FreeRefl (OneTruncation₂ V) ⥤ V.HomotopyCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A canonical functor from the free category on the refl quiver underlying a 2-tru
ncated
simplicial set `V` to its homotopy category.
-/
def quotientFunctor :
    Cat.FreeRefl (OneTruncation₂ V) ⥤ V.HomotopyCategory :=
  Quotient.functor _
/-
**SSet.Truncated.HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated.Hom
otopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotientFunctor V).Full :=
  Quotient.full_functor _

variable {V}

/-- Constructor for objects of the homotopy category of a `2`-truncated simplicial set. -/
/-
**SSet.Truncated.HomotopyCategory.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.H
omotopyCategory`。
形式化陈述：mk (x : V _⦋0⦌₂) : V.HomotopyCategory
参数：x : V _⦋0⦌₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects of the homotopy category of a `2`-truncated simplicial s
et.
-/
def mk (x : V _⦋0⦌₂) : V.HomotopyCategory :=
  (quotientFunctor V).obj (.mk x)
/-
**SSet.Truncated.HomotopyCategory.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
Truncated.HomotopyCategory`。
形式化陈述：mk_surjective : Function.Surjective (mk (V
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_surjective : Function.Surjective (mk (V := V)) := by
  rintro ⟨⟨x⟩⟩
  exact ⟨x, rfl⟩
/-
**SSet.Truncated.HomotopyCategory.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.
HomotopyCategory`。
形式化陈述：ext {x y : V.HomotopyCategory} (h : x.as.as = y.as.as) : x = y
参数：h : x.as.as = y.as.as。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.HomotopyCategory.mk_surjective`：mk_surjective : Function.
Surjective (mk (V
-/
lemma ext {x y : V.HomotopyCategory} (h : x.as.as = y.as.as) : x = y := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  obtain rfl : x = y := h
  rfl

@[elab_as_elim, cases_eliminator]
/-
**SSet.Truncated.HomotopyCategory.cases_on** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Trunc
ated.HomotopyCategory`。
形式化陈述：∀ {V : SSet.Truncated 2} {motive : V.HomotopyCategory → Prop},   (∀ (x : V
.obj (Opposite.op { obj := { len := 0 }, property := SSet.OneTruncation₂._proof_
1 })),       motive (SSet.Truncated.HomotopyCategory.mk x)) →     ∀ (x : V.Homot
opyCategory), motive x
参数：∀ (x : V.obj (Opposite.op { obj := { len := 0 }, property := SSet.OneTruncati
on₂._proof_1 })),       motive (SSet.Truncated.HomotopyCategory.mk x)；x : V.Homo
topyCategory。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.HomotopyCategory.mk_surjective`：mk_surjective : Function.
Surjective (mk (V
-/
protected lemma cases_on {motive : V.HomotopyCategory → Prop}
    (h : ∀ (x : V _⦋0⦌₂), motive (.mk x))
    (x : V.HomotopyCategory) :
    motive x := by
  obtain ⟨x', rfl⟩ := mk_surjective x
  exact h x'

/-- The morphism in the homotopy category of a `2`-truncated simplicial set that
is induced by an edge. -/
/-
**SSet.Truncated.HomotopyCategory.homMk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncate
d.HomotopyCategory`。
形式化陈述：homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁) : mk x₀ ⟶ mk x₁
参数：e : Edge x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in the homotopy category of a `2`-truncated simplicial set that
is induced by an edge.
-/
def homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁) : mk x₀ ⟶ mk x₁ :=
  (quotientFunctor V).map (Cat.FreeRefl.homMk e)
/-
**SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Truncated.HomotopyCategory`。
形式化陈述：congr_arrowMk_homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁) {y₀ y₁ : V _⦋0⦌₂} (
e' : Edge y₀ y₁) (h : e.edge = e'.edge) : Arrow.mk (homMk e) = Arrow.mk (homMk e
')
参数：e : Edge x₀ x₁；e' : Edge y₀ y₁；h : e.edge = e'.edge。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.ext`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opposi
te.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   {x y
 : SSet.Trunc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.Truncated.Edge.tgt_eq`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opp
osite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   (
self : SSet.Trun…
· 使用定理 `SSet.Truncated.Edge.src_eq`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opp
osite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   (
self : SSet.Trun…
-/
lemma congr_arrowMk_homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : V _⦋0⦌₂} (e' : Edge y₀ y₁) (h : e.edge = e'.edge) :
    Arrow.mk (homMk e) = Arrow.mk (homMk e') := by
  obtain rfl : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := by aesop
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.homMk_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Trunc
ated.HomotopyCategory`。
形式化陈述：homMk_id (x : V _⦋0⦌₂) : homMk (.id x) = 𝟙 (mk x)
参数：x : V _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Truncated.HomotopyCategory.homMk.eq_1`：∀ {V : SSet.Truncated 2} {x₀
 x₁ : V.obj (Opposite.op { obj := { len := 0 }, property := SSet.OneTruncation₂.
_proof_1 })}   (e : SSet.Truncat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.OneTruncation₂.reflQuiver_id`：∀ (S : SSet.Truncated 2) (x : S.obj (
Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })),
   CategoryTheory.ReflQ…
· 使用引理 `CategoryTheory.Cat.FreeRefl.homMk_id`：homMk_id (v : V) : homMk (𝟙rq v) =
 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma homMk_id (x : V _⦋0⦌₂) :
    homMk (.id x) = 𝟙 (mk x) := by
  rw [homMk, ← OneTruncation₂.reflQuiver_id, Cat.FreeRefl.homMk_id,
    CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
/-
**SSet.Truncated.HomotopyCategory.homMk_comp_homMk** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.Truncated.HomotopyCategory`。
形式化陈述：homMk_comp_homMk {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂
} {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) : homMk e₀₁ ≫ homMk e₁₂ =
 homMk e₀₂
参数：h : Edge.CompStruct e₀₁ e₁₂ e₀₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
lemma homMk_comp_homMk {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ := by
  simpa [homMk] using! CategoryTheory.Quotient.sound _
    (OneTruncation₂.HoRel₂.of_compStruct h)

variable (V) in
/-- If `V` is a `2`-truncated simplicial sets, this is the family of
morphisms in `V.HomotopyCategory` corresponding to the edges of `V`.
(Any morphism in `V.HomotopyCategory` is in the multiplicative closure
of this family of morphisms, see `multiplicativeClosure_morphismPropertyHomMk`.) -/
/-
**SSet.Truncated.HomotopyCategory.morphismPropertyHomMk** 是 Mathlib 中的一个定义，位于命名空
间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：morphismPropertyHomMk : MorphismProperty V.HomotopyCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` is a `2`-truncated simplicial sets, this is the family of
morphisms in `V.HomotopyCategory` corresponding to the edges of `V`.
(Any morphism in `V.HomotopyCategory` is in the multiplicative closure
of this family of morphisms, see `multiplicativeClosure_morphismPropertyHomMk`.)
-/
def morphismPropertyHomMk : MorphismProperty V.HomotopyCategory :=
  .ofHoms (fun (e : Σ (x y : V _⦋0⦌₂), Edge x y) ↦ homMk e.2.2)
/-
**SSet.Truncated.HomotopyCategory.morphismPropertyHomMk_of_edge** 是 Mathlib 中的一个
引理，位于命名空间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：morphismPropertyHomMk_of_edge {x y : V _⦋0⦌₂} (e : Edge x y) : morphismPro
pertyHomMk V (homMk e)
参数：e : Edge x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
-/
lemma morphismPropertyHomMk_of_edge {x y : V _⦋0⦌₂} (e : Edge x y) :
    morphismPropertyHomMk V (homMk e) := by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩
/-
**SSet.Truncated.HomotopyCategory.morphismPropertyHomMk_eq_strictMap** 是 Mathlib
 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：morphismPropertyHomMk_eq_strictMap : morphismPropertyHomMk V = (Cat.FreeRe
fl.morphismPropertyHomMk (OneTruncation₂ V)).strictMap (quotientFunctor V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用引理 `CategoryTheory.MorphismProperty.map_mem_strictMap`：map_mem_strictMap (P 
: MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) : (P.strictMa
p F) (F.map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `SSet.Truncated.HomotopyCategory.morphismPropertyHomMk_of_edge`：morphismP
ropertyHomMk_of_edge {x y : V _⦋0⦌₂} (e : Edge x y) : morphismPropertyHomMk V (h
omMk e)
-/
lemma morphismPropertyHomMk_eq_strictMap :
    morphismPropertyHomMk V =
      (Cat.FreeRefl.morphismPropertyHomMk (OneTruncation₂ V)).strictMap (quotientFunctor V) := by
  ext _ _ f
  constructor
  · rintro ⟨_⟩
    exact MorphismProperty.map_mem_strictMap _ _ _ ⟨_⟩
  · rintro ⟨⟨_, _, e⟩⟩
    exact morphismPropertyHomMk_of_edge e

open MorphismProperty in
/-
**SSet.Truncated.HomotopyCategory.multiplicativeClosure_morphismPropertyHomMk** 
是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：multiplicativeClosure_morphismPropertyHomMk : (morphismPropertyHomMk V).mu
ltiplicativeClosure = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `SSet.Truncated.HomotopyCategory.instFullFreeReflOneTruncation₂QuotientFu
nctor`：∀ (V : SSet.Truncated 2), (SSet.Truncated.HomotopyCategory.quotientFuncto
r V).Full
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.morphismPropertyHomMk_eq_strictMap`：morp
hismPropertyHomMk_eq_strictMap : morphismPropertyHomMk V = (Cat.FreeRefl.morphis
mPropertyHomMk (OneTruncation₂ V)).strictMap (quotientFu…
· 使用引理 `CategoryTheory.MorphismProperty.strictMap_multiplicativeClosure_le`：stri
ctMap_multiplicativeClosure_le (F : C ⥤ D) : W.multiplicativeClosure.strictMap F
 <= (W.strictMap F).multiplicativeClosure
· 使用引理 `CategoryTheory.Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk`
：multiplicativeClosure_morphismPropertyHomMk : (morphismPropertyHomMk V).multipl
icativeClosure = ⊤
· 使用引理 `CategoryTheory.MorphismProperty.map_mem_strictMap`：map_mem_strictMap (P 
: MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) : (P.strictMa
p F) (F.map f)
-/
lemma multiplicativeClosure_morphismPropertyHomMk :
    (morphismPropertyHomMk V).multiplicativeClosure = ⊤ :=
  le_antisymm (by simp) (fun x y f _ ↦ by
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    rw [morphismPropertyHomMk_eq_strictMap]
    refine strictMap_multiplicativeClosure_le _ _ _ ?_
    rw [Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk]
    exact map_mem_strictMap _ _ _ (by simp))
/-
**SSet.Truncated.HomotopyCategory.morphismProperty_eq_top** 是 Mathlib 中的一个引理，位于命
名空间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：morphismProperty_eq_top {W : MorphismProperty V.HomotopyCategory} [W.IsMul
tiplicative] (hW : forall {x y : V _⦋0⦌₂} (e : Edge x y), W (homMk e)) : W = ⊤
参数：hW : forall {x y : V _⦋0⦌₂} (e : Edge x y), W (homMk e)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Truncated.HomotopyCategory.multiplicativeClosure_morphismPropertyHo
mMk`：multiplicativeClosure_morphismPropertyHomMk : (morphismPropertyHomMk V).mul
tiplicativeClosure = ⊤
· 使用引理 `CategoryTheory.MorphismProperty.multiplicativeClosure_le_iff`：multiplica
tiveClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] : multiplicat
iveClosure W <= W' ↔ W <= W' where .trans h mp h
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma morphismProperty_eq_top {W : MorphismProperty V.HomotopyCategory}
    [W.IsMultiplicative]
    (hW : ∀ {x y : V _⦋0⦌₂} (e : Edge x y), W (homMk e)) :
    W = ⊤ :=
  le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk,
      MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨_, _, e⟩
    exact hW e)

section

variable {D : Type*} [Category* D]

section

variable (obj : V _⦋0⦌₂ → D) (map : ∀ {x y : V _⦋0⦌₂}, Edge x y → (obj x ⟶ obj y))
  (map_id : ∀ (x : V _⦋0⦌₂), map (.id x) = 𝟙 _)
  (map_comp : ∀ {x₀ x₁ x₂ : V _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂), map e₀₁ ≫ map e₁₂ = map e₀₂)

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for functors from the homotopy category. -/
/-
**SSet.Truncated.HomotopyCategory.lift** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated
.HomotopyCategory`。
形式化陈述：lift : V.HomotopyCategory ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for functors from the homotopy category.
-/
def lift : V.HomotopyCategory ⥤ D :=
  CategoryTheory.Quotient.lift _
    (Cat.FreeRefl.lift' obj (fun f ↦ map f) map_id) (by
      rintro _ _ _ _ ⟨h⟩
      simp only [Functor.map_comp]
      convert! map_comp h <;> apply Cat.FreeRefl.lift'_map)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.lift_obj_mk** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Tr
uncated.HomotopyCategory`。
形式化陈述：lift_obj_mk (x : V _⦋0⦌₂) : (lift obj map map_id map_comp).obj (mk x) = ob
j x
参数：x : V _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_obj_mk (x : V _⦋0⦌₂) : (lift obj map map_id map_comp).obj (mk x) = obj x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.lift_map_homMk** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Truncated.HomotopyCategory`。
形式化陈述：lift_map_homMk {x y : V _⦋0⦌₂} (e : Edge x y) : (lift obj map map_id map_c
omp).map (homMk e) = map e
参数：e : Edge x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma lift_map_homMk {x y : V _⦋0⦌₂} (e : Edge x y) :
    (lift obj map map_id map_comp).map (homMk e) = map e :=
  Category.id_comp _

end

variable {F G : V.HomotopyCategory ⥤ D}

section

variable (φ : ∀ (x : V _⦋0⦌₂), F.obj (mk x) ⟶ G.obj (mk x))
  (hφ : ∀ ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y),
    F.map (homMk e) ≫ φ y = φ x ≫ G.map (homMk e) := by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-- Constructor for natural transformations between functors from `V.HomotopyCategory`. -/
/-
**SSet.Truncated.HomotopyCategory.mkNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Tru
ncated.HomotopyCategory`。
形式化陈述：mkNatTrans : F ⟶ G where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations between functors from `V.HomotopyCategor
y`.
-/
def mkNatTrans : F ⟶ G where
  app _ := φ _
  naturality _ _ f := by
    have : MorphismProperty.naturalityProperty (fun (x : V.HomotopyCategory) ↦ φ _) = ⊤ :=
      morphismProperty_eq_top (fun e ↦ hφ e)
    exact this.symm.le f (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.mkNatTrans_app_mk** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.Truncated.HomotopyCategory`。
形式化陈述：mkNatTrans_app_mk (v : V _⦋0⦌₂) : (mkNatTrans φ hφ).app (mk v) = φ v
参数：v : V _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkNatTrans_app_mk (v : V _⦋0⦌₂) :
    (mkNatTrans φ hφ).app (mk v) = φ v := rfl

end

section

variable (iso : ∀ (x : V _⦋0⦌₂), F.obj (mk x) ≅ G.obj (mk x))
  (hiso : ∀ ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y), F.map (homMk e) ≫ (iso y).hom =
    (iso x).hom ≫ G.map (homMk e) := by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-- Constructor for natural isomorphisms between functors from `V.HomotopyCategory`. -/
/-
**SSet.Truncated.HomotopyCategory.mkNatIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Trunc
ated.HomotopyCategory`。
形式化陈述：mkNatIso : F ≅ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural isomorphisms between functors from `V.HomotopyCategory`.
-/
def mkNatIso : F ≅ G :=
  NatIso.ofComponents (fun _ ↦ iso _) (fun f ↦ (mkNatTrans _ hiso).naturality f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.mkNatIso_hom_app_mk** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Truncated.HomotopyCategory`。
形式化陈述：mkNatIso_hom_app_mk (v : V _⦋0⦌₂) : (mkNatIso iso hiso).hom.app (mk v) = (
iso v).hom
参数：v : V _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkNatIso_hom_app_mk (v : V _⦋0⦌₂) :
    (mkNatIso iso hiso).hom.app (mk v) = (iso v).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.mkNatIso_inv_app_mk** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Truncated.HomotopyCategory`。
形式化陈述：mkNatIso_inv_app_mk (v : V _⦋0⦌₂) : (mkNatIso iso hiso).inv.app (mk v) = (
iso v).inv
参数：v : V _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkNatIso_inv_app_mk (v : V _⦋0⦌₂) :
    (mkNatIso iso hiso).inv.app (mk v) = (iso v).inv := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.functor_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Tr
uncated.HomotopyCategory`。
形式化陈述：functor_ext {F G : V.HomotopyCategory ⥤ D} (h₁ : forall (x : V _⦋0⦌₂), F.o
bj (mk x) = G.obj (mk x)) (h₂ : forall ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y), F.map (ho
mMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm) : F = G
参数：h₁ : forall (x : V _⦋0⦌₂), F.obj (mk x) = G.obj (mk x)；h₂ : forall ⦃x y : V _
⦋0⦌₂⦄ (e : Edge x y), F.map (homMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToH
om (h₁ y).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functor_ext {F G : V.HomotopyCategory ⥤ D}
    (h₁ : ∀ (x : V _⦋0⦌₂), F.obj (mk x) = G.obj (mk x))
    (h₂ : ∀ ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y),
      F.map (homMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm) :
    F = G :=
  Functor.ext_of_iso (mkNatIso (fun x ↦ eqToIso (h₁ x))
    (fun _ _ e ↦ by simp [h₂ e])) (fun _ ↦ h₁ _)

end

/-
**SSet.Truncated.HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated.Hom
otopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Truncated.{u} 2) [Subsingleton (X _⦋0⦌₂)] :
    Subsingleton X.HomotopyCategory where
  allEq x y := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain rfl := Subsingleton.elim x y
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.subsingleton_hom** 是 Mathlib 中的一个实例，位于命名空间 `SS
et.Truncated.HomotopyCategory`。
形式化陈述：subsingleton_hom (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X
 _⦋1⦌₂)] (x y : X.HomotopyCategory) : Subsingleton (x ⟶ y)
参数：X : Truncated.{u} 2；X _⦋0⦌₂；X _⦋1⦌₂；x y : X.HomotopyCategory。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.instSubsingletonHom`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] (r : HomRel C) [∀ (x y : C), Subsingleton (x
 ⟶ y)]   (x y : CategoryTheory.Qu…
· 使用定理 `CategoryTheory.Cat.FreeRefl.instSubsingletonHomOfUnique`：∀ (V : Type u_2
) [inst : CategoryTheory.ReflQuiver V] [Unique V] [∀ (x y : V), Subsingleton (x 
⟶ y)]   (x y : CategoryTheory.Cat.FreeRefl V)…
-/
instance subsingleton_hom (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
    (x y : X.HomotopyCategory) :
    Subsingleton (x ⟶ y) :=
  letI : Unique (OneTruncation₂ X) := inferInstanceAs (Unique (X _⦋0⦌₂))
  letI (x y : (OneTruncation₂ X)) : Subsingleton (x ⟶ y) :=
    inferInstanceAs (Subsingleton <| X.Edge _ _)
  CategoryTheory.Quotient.instSubsingletonHom _ _ _
/-
**SSet.Truncated.HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated.Hom
otopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] : Unique X.HomotopyCategory :=
  letI : Unique (OneTruncation₂ X) := inferInstanceAs (Unique (X _⦋0⦌₂))
  CategoryTheory.Quotient.instUnique _

/-- If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
then `X.HomotopyCategory` is a terminal object in `Cat`. -/
/-
**SSet.Truncated.HomotopyCategory.isTerminal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Tru
ncated.HomotopyCategory`。
形式化陈述：isTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂
)] : IsTerminal (Cat.of X.HomotopyCategory)
参数：X : Truncated.{u} 2；X _⦋0⦌₂；X _⦋1⦌₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
then `X.HomotopyCategory` is a terminal object in `Cat`.
-/
def isTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    IsTerminal (Cat.of X.HomotopyCategory) :=
  letI : IsDiscrete (X.HomotopyCategory) := { eq_of_hom := by subsingleton }
  Cat.isTerminalOfUniqueOfIsDiscrete

end HomotopyCategory

section

open HomotopyCategory

variable {V W} (f : V ⟶ W)

/-- A map of 2-truncated simplicial sets induces a functor between homotopy categories. -/
/-
**SSet.Truncated.mapHomotopyCategory** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：mapHomotopyCategory : V.HomotopyCategory ⥤ W.HomotopyCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map of 2-truncated simplicial sets induces a functor between homotopy categori
es.
-/
def mapHomotopyCategory :
    V.HomotopyCategory ⥤ W.HomotopyCategory :=
  CategoryTheory.Quotient.lift _
    (((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙ quotientFunctor W) (by
      rintro _ _ _ _ ⟨h⟩
      exact CategoryTheory.Quotient.sound _ ⟨h.map f⟩)

@[simp]
/-
**SSet.Truncated.mapHomotopyCategory_obj** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncat
ed`。
形式化陈述：mapHomotopyCategory_obj (x : V _⦋0⦌₂) : (mapHomotopyCategory f).obj (.mk x
) = .mk (f.app _ x)
参数：x : V _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapHomotopyCategory_obj (x : V _⦋0⦌₂) :
    (mapHomotopyCategory f).obj (.mk x) = .mk (f.app _ x) := rfl

@[simp]
/-
**SSet.Truncated.mapHomotopyCategory_homMk** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Trunc
ated`。
形式化陈述：mapHomotopyCategory_homMk {x y : V _⦋0⦌₂} (e : Edge x y) : (mapHomotopyCat
egory f).map (homMk e) = homMk (e.map f)
参数：e : Edge x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapHomotopyCategory_homMk {x y : V _⦋0⦌₂} (e : Edge x y) :
    (mapHomotopyCategory f).map (homMk e) = homMk (e.map f) := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor that takes a 2-truncated simplicial set to its homotopy category. -/
/-
**SSet.Truncated.hoFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that takes a 2-truncated simplicial set to its homotopy category.
-/
def hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u, u} where
  obj V := Cat.of V.HomotopyCategory
  map F := (mapHomotopyCategory F).toCatHom
  map_id _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)
  map_comp _ _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)
/-
**SSet.Truncated.hoFunctor** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    ((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙
      SSet.Truncated.HomotopyCategory.quotientFunctor Y =
      SSet.Truncated.HomotopyCategory.quotientFunctor X ⋙ mapHomotopyCategory f := rfl

/-- By `Quotient.lift_unique'` (not `Quotient.lift`) we have that `quotientFunctor V` is an
epimorphism. -/
/-
**SSet.Truncated.HomotopyCategory.lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 `SSet.T
runcated.HomotopyCategory`。
形式化陈述：∀ (V : SSet.Truncated 2) {D : Type u_1} [inst : CategoryTheory.Category.{v
_1, u_1} D]   (F₁ F₂ : CategoryTheory.Functor V.HomotopyCategory D),   (SSet.Tru
ncated.HomotopyCategory.quotientFunctor V).comp F₁ =       (SSet.Truncated.Homot
opyCategory.quotientFunctor V).comp F₂ →     F₁ = F₂
参数：V : SSet.Truncated 2；F₁ F₂ : CategoryTheory.Functor V.HomotopyCategory D；SSet
.Truncated.HomotopyCategory.quotientFunctor V；SSet.Truncated.HomotopyCategory.qu
otientFunctor V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Quotient.lift_unique'`：lift_unique' (F₁ F₂ : Quotient r ⥤
 D) (h : functor r ⋙ F₁ = functor r ⋙ F₂) : F₁ = F₂

--- 原说明 ---
By `Quotient.lift_unique'` (not `Quotient.lift`) we have that `quotientFunctor V
` is an
epimorphism.
-/
theorem HomotopyCategory.lift_unique' (V : SSet.Truncated.{u} 2) {D : Type*} [Category* D]
    (F₁ F₂ : V.HomotopyCategory ⥤ D)
    (h : HomotopyCategory.quotientFunctor V ⋙ F₁ = HomotopyCategory.quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' _ _ _ h

end Truncated

/-- The functor that takes a simplicial set to its homotopy category by passing through the
2-truncation. -/
/-
**SSet.hoFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：hoFunctor : SSet.{u} ⥤ Cat.{u, u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that takes a simplicial set to its homotopy category by passing thro
ugh the
2-truncation.
-/
def hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ Truncated.hoFunctor₂

/-- For a simplicial set `X`, the underlying type of `hoFunctor.obj X` is equivalent to `X _⦋0⦌`. -/
/-
**SSet.hoFunctor.obj.equiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.hoFunctor.obj`。
形式化陈述：(X : _root_.SSet) → ↑(SSet.hoFunctor.obj X) ≃ X.obj (Opposite.op { len := 
0 })
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
For a simplicial set `X`, the underlying type of `hoFunctor.obj X` is equivalent
 to `X _⦋0⦌`.
-/
def hoFunctor.obj.equiv (X : SSet) : hoFunctor.obj X ≃ X _⦋0⦌ :=
  (Quotient.equiv.{u, u} _).trans (Quotient.equiv _)

/-- Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique point and thus
`OneTruncation₂ ((truncation 2).obj Δ[0])` has a unique inhabitant. -/
/-
**SSet.instUniqueOneTruncation** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique point and thus
`OneTruncation₂ ((truncation 2).obj Δ[0])` has a unique inhabitant.
-/
instance instUniqueOneTruncation₂DeltaZero : Unique (OneTruncation₂ ((truncation 2).obj Δ[0])) :=
  inferInstanceAs (Unique (ULift.{_, 0} (⦋0⦌ ⟶ ⦋0⦌)))

/-- Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique edge and thus the homs of
`OneTruncation₂ ((truncation 2).obj Δ[0])` have unique inhabitants. -/
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique edge and thus the
 homs of
`OneTruncation₂ ((truncation 2).obj Δ[0])` have unique inhabitants.
-/
instance (x y : OneTruncation₂ ((truncation 2).obj Δ[0])) : Unique (x ⟶ y) where
  default := by
    obtain rfl : x = default := Unique.uniq _ _
    obtain rfl : y = default := Unique.uniq _ _
    exact 𝟙rq instUniqueOneTruncation₂DeltaZero.default
  uniq _ := by
    let : Subsingleton (((truncation 2).obj Δ[0]).obj (.op ⦋1⦌₂)) :=
      inferInstanceAs (Subsingleton (ULift.{_, 0} (⦋1⦌ ⟶ ⦋0⦌)))
    ext
    exact this.allEq _ _
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique ((truncation.{u} 2).obj Δ[0]).HomotopyCategory :=
  inferInstanceAs (Unique <| CategoryTheory.Quotient _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscrete ((truncation.{u} 2).obj Δ[0]).HomotopyCategory where
  subsingleton x y :=
    inferInstanceAs (Subsingleton ((_ : CategoryTheory.Quotient _) ⟶ _))
  eq_of_hom _ := by subsingleton

/-- The category `hoFunctor.obj (Δ[0])` is terminal. -/
/-
**SSet.isTerminalHoFunctorDeltaZero** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：isTerminalHoFunctorDeltaZero : IsTerminal (hoFunctor.{u}.obj (Δ[0]))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.instIsDiscreteHomotopyCategoryObjTruncatedOfNatNatTruncationSimplex
CategoryStdSimplexMk`：CategoryTheory.IsDiscrete ((SSet.truncation 2).obj (SSet.s
tdSimplex.obj { len := 0 })).HomotopyCategory

--- 原说明 ---
The category `hoFunctor.obj (Δ[0])` is terminal.
-/
def isTerminalHoFunctorDeltaZero : IsTerminal (hoFunctor.{u}.obj (Δ[0])) :=
  Cat.isTerminalOfUniqueOfIsDiscrete

/-- The homotopy category functor preserves generic terminal objects. -/
/-
**SSet.hoFunctor.terminalIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.hoFunctor`。
形式化陈述：SSet.hoFunctor.obj (⊤_ _root_.SSet) ≅ ⊤_ CategoryTheory.Cat
参数：⊤_ _root_.SSet。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Cat.instHasTerminal`：CategoryTheory.Limits.HasTerminal Ca
tegoryTheory.Cat

--- 原说明 ---
The homotopy category functor preserves generic terminal objects.
-/
noncomputable def hoFunctor.terminalIso : hoFunctor.obj (⊤_ SSet) ≅ ⊤_ Cat :=
  hoFunctor.mapIso (terminalIsoIsTerminal stdSimplex.isTerminalObj₀) ≪≫
    (terminalIsoIsTerminal isTerminalHoFunctorDeltaZero).symm
/-
**SSet.hoFunctor.preservesTerminal** 是 Mathlib 中的一个定理，位于命名空间 `SSet.hoFunctor`。
形式化陈述：CategoryTheory.Limits.PreservesLimit (CategoryTheory.Functor.empty _root_.
SSet) SSet.hoFunctor
参数：CategoryTheory.Functor.empty _root_.SSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesTerminal_of_iso`：preservesTerminal_of_iso
 (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Cat.instHasTerminal`：CategoryTheory.Limits.HasTerminal Ca
tegoryTheory.Cat
-/
instance hoFunctor.preservesTerminal : PreservesLimit (empty.{0} SSet) hoFunctor :=
  preservesTerminal_of_iso hoFunctor hoFunctor.terminalIso
/-
**SSet.hoFunctor.preservesTerminal'** 是 Mathlib 中的一个定理，位于命名空间 `SSet.hoFunctor`。
形式化陈述：CategoryTheory.Limits.PreservesLimitsOfShape (CategoryTheory.Discrete PEmp
ty.{1}) SSet.hoFunctor
参数：CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal
`：preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.em
pty.{0} C) G] : PreservesLimitsOfShape (Discrete PEmpty.{1}) G…
· 使用定理 `SSet.hoFunctor.preservesTerminal`：CategoryTheory.Limits.PreservesLimit (
CategoryTheory.Functor.empty _root_.SSet) SSet.hoFunctor
-/
instance hoFunctor.preservesTerminal' :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) hoFunctor :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end SSet

