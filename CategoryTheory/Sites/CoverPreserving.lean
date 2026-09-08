/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Tactic.ApplyFun
/-!
# Cover-preserving functors between sites.

In order to show that a functor is continuous, we define cover-preserving functors
between sites as functors that push covering sieves to covering sieves.
Then, a cover-preserving and compatible-preserving functor is continuous.

## Main definitions

* `CategoryTheory.CoverPreserving`: a functor between sites is cover-preserving if it
  pushes covering sieves to covering sieves
* `CategoryTheory.CompatiblePreserving`: a functor between sites is compatible-preserving
  if it pushes compatible families of elements to compatible families.

## Main results

- `CategoryTheory.isContinuous_of_coverPreserving`: If `G : C ⥤ D` is
  cover-preserving and compatible-preserving, then `G` is a continuous functor,
  i.e. `G.op ⋙ -` as a functor `(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WU

-/

public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory Opposite CategoryTheory.Presieve.FamilyOfElements CategoryTheory.Presieve
  CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {A : Type u₃} [Category.{v₃} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology A}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.functorPushforward G` is a covering sieve in `D`.
-/
/-
**CategoryTheory.CoverPreserving** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.GrothendieckTopology C →           CategoryTheory.GrothendieckTopology D 
→ CategoryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.functorPushforward G` is a covering si
eve in `D`.
-/
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (_ : S ∈ J U), S.functorPushforward G ∈ K (G.obj U)

/-- The identity functor on a site is cover-preserving. -/
/-
**CategoryTheory.idCoverPreserving** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：idCoverPreserving : CoverPreserving J J (𝟭 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPushforward_id`：functorPushforward_id (R : S
ieve X) : R.functorPushforward (𝟭 _) = R

--- 原说明 ---
The identity functor on a site is cover-preserving.
-/
theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun hS => by simpa using! hS⟩

/-- The composition of two cover-preserving functors is cover-preserving. -/
/-
**CategoryTheory.CoverPreserving.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
CoverPreserving`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {A : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} A] (J : CategoryTheory.GrothendieckTopology C)   (K : C
ategoryTheory.GrothendieckTopology D) {L : CategoryTheory.GrothendieckTopology A
}   {F : CategoryTheory.Functor C D},   CategoryTheory.CoverPreserving J K F →  
   ∀ {G : CategoryTheory.Functor D A},       CategoryTheory.CoverPreserving K L 
G → CategoryTheory.CoverPreserving J L (F.comp G)
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPushforward_comp`：functorPushforward_comp (R
 : Sieve X) : R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPus
hforward G
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…

--- 原说明 ---
The composition of two cover-preserving functors is cover-preserving.
-/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functorPushforward` used.
-/
/-
**CategoryTheory.CompatiblePreserving** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.GrothendieckTopology D → CategoryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if
 for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commutin
g diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via 
`fᵢ`.
This is actually stronger than merely preserving compatible families because of 
the definition of
`functorPushforward` used.
-/
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  compatible :
    ∀ (ℱ : Sheaf K (Type w)) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T}
      (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.obj.map f₁.op (x g₁ hg₁) = ℱ.obj.map f₂.op (x g₂ hg₂)

section
variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : Sheaf K (Type w)) {Z : C}
variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T} (h : x.Compatible)
include hG h

/-- `CompatiblePreserving` functors indeed preserve compatible families. -/
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.functorPushforward** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {K : CategoryTheory.Grothendieck
Topology D} {G : CategoryTheory.Functor C D},   CategoryTheory.CompatiblePreserv
ing K G →     ∀ (ℱ : CategoryTheory.Sheaf K (Type w)) {Z : C} {T : CategoryTheor
y.Presieve Z}       {x : CategoryTheory.Presieve.FamilyOfElements (G.op.comp ℱ.o
bj) T},       x.Compatible → (CategoryTheory.Presieve.FamilyOfElements.functorPu
shforward G x).Compatible
参数：ℱ : CategoryTheory.Sheaf K (Type w)；G.op.comp ℱ.obj；CategoryTheory.Presieve.F
amilyOfElements.functorPushforward G x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CompatiblePreserving.compatible`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {K : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …

--- 原说明 ---
`CompatiblePreserving` functors indeed preserve compatible families.
-/
theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.obj.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.obj.map (g₂ ≫ h₂).op (x f₂ hf₂) by
    simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using eq

@[simp]
/-
**CategoryTheory.CompatiblePreserving.apply_map** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.CompatiblePreserving`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {K : CategoryTheory.Grothendieck
Topology D} {G : CategoryTheory.Functor C D},   CategoryTheory.CompatiblePreserv
ing K G →     ∀ (ℱ : CategoryTheory.Sheaf K (Type w)) {Z : C} {T : CategoryTheor
y.Presieve Z}       {x : CategoryTheory.Presieve.FamilyOfElements (G.op.comp ℱ.o
bj) T},       x.Compatible →         ∀ {Y : C} {f : Y ⟶ Z} (hf : T f),          
 CategoryTheory.Presieve.FamilyOfElements.functorPushforward G x (G.map f) ⋯ = x
 f hf
参数：ℱ : CategoryTheory.Sheaf K (Type w)；G.op.comp ℱ.obj；hf : T f；G.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.image_mem_functorPushforward`：image_mem_functorP
ushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) : R.functorPushforward F (F.ma
p f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.CompatiblePreserving.compatible`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {K : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.functorPushforward G (G.map f) (image_mem_functorPushforward G T hf) = x f hf := by
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])

end

open Limits.WalkingCospan

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.compatiblePreservingOfFlat** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [
Category.{v₂} D] (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] 
: CompatiblePreserving K G
参数：K : GrothendieckTopology D；G : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cone.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
    over it since `StructuredArrow W u` is cofiltered.
    Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
    -/
  let c' := IsCofiltered.cone (c.toStructuredArrow ⋙ StructuredArrow.pre _ _ _)
  have eq₁ : f₁ = (c'.pt.hom ≫ G.map (c'.π.app left).right) ≫ eqToHom (by simp) := by simp [c]
  have eq₂ : f₂ = (c'.pt.hom ≫ G.map (c'.π.app right).right) ≫ eqToHom (by simp) := by simp [c]
  conv_lhs => rw [eq₁]
  conv_rhs => rw [eq₂]
  simp only [c, op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
  apply congr_arg -- Porting note: was `congr 1` which for some reason doesn't do anything here
  -- despite goal being of the form f a = f b, with f=`ℱ.val.map (Quiver.Hom.op c'.pt.hom)`
  /-
    Since everything now falls in the image of `u`,
    the result follows from the compatibility of `x` in the image of `u`.
    -/
  injection c'.π.naturality WalkingCospan.Hom.inl with _ e₁
  injection c'.π.naturality WalkingCospan.Hom.inr with _ e₂
  exact hx (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.compatiblePreservingOfDownwardsClosed** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [F.Full] [F.Faithful] (h
F : forall {c : C} {d : D} (_ : d ⟶ F.obj c), Σ c', F.obj c' ≅ d) : CompatiblePr
eserving K F
参数：F : C ⥤ D；hF : forall {c : C} {d : D} (_ : d ⟶ F.obj c), Σ c', F.obj c' ≅ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.mapIso_hom`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  (F : CategoryTheory.F…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [F.Full] [F.Faithful]
    (hF : ∀ {c : C} {d : D} (_ : d ⟶ F.obj c), Σ c', F.obj c' ≅ d) : CompatiblePreserving K F := by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← Functor.map_comp_apply]
  simpa using!
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by simpa using! he)

variable {F J K}

/-- If `F` is cover-preserving and compatible-preserving, then `F` is a continuous functor. -/
@[stacks 00WW "This is basically this Stacks entry."]
/-
**CategoryTheory.Functor.isContinuous_of_coverPreserving** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {J : CategoryTheory.GrothendieckTopology C}   {K : CategoryTheory.GrothendieckT
opology D},   CategoryTheory.CompatiblePreserving K F → CategoryTheory.CoverPres
erving J K F → F.IsContinuous J K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.functorPushforward`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_
1 : CategoryTheory.Category.{v₂, u₂} D]   {K : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presieve.image_mem_functorPushforward`：image_mem_functorP
ushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) : R.functorPushforward F (F.ma
p f)
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isAmalgamation`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.CompatiblePreserving.apply_map`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `F` is cover-preserving and compatible-preserving, then `F` is a continuous f
unctor.
-/
lemma Functor.isContinuous_of_coverPreserving (hF₁ : CompatiblePreserving.{max u₁ v₁ u₂ v₂} K F)
    (hF₂ : CoverPreserving J K F) : Functor.IsContinuous F J K where
  op_comp_isSheaf_of_types G X S hS x hx := by
    apply existsUnique_of_exists_of_unique
    · have H := (isSheaf_iff_isSheaf_of_type _ _).1 G.2 _ (hF₂.cover_preserve hS)
      exact ⟨H.amalgamate (x.functorPushforward F) (hx.functorPushforward hF₁),
        fun V f hf => (H.isAmalgamation (hx.functorPushforward hF₁) (F.map f) _).trans
          (hF₁.apply_map _ hx hf)⟩
    · intro y₁ y₂ hy₁ hy₂
      apply (((isSheaf_iff_isSheaf_of_type _ _).1 G.2).isSeparated _ (hF₂.cover_preserve hS)).ext
      rintro Y _ ⟨Z, g, h, hg, rfl⟩
      simpa using! congrArg _ ((hy₁ g hg).trans (hy₂ g hg).symm)

variable (F J K) in
/-- Continuous functors send covering sieves to covering sieves.
The converse is false, see [SGA4, III, Exemple 1.9.3][sga-4-tome-1]. -/
/-
**CategoryTheory.CoverPreserving.of_isContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CoverPreserving`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 (J : CategoryTheory.GrothendieckTopology C)   (K : CategoryTheory.GrothendieckT
opology D) [F.IsContinuous J K], CategoryTheory.CoverPreserving J K F
参数：F : CategoryTheory.Functor C D；J : CategoryTheory.GrothendieckTopology C；K : 
CategoryTheory.GrothendieckTopology D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.mem_iff_isSheafFor_closedSieves`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothe
ndieckTopology C) {X : C}   (S : CategoryTheory.Sieve X),…
· 使用引理 `CategoryTheory.Sieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Sieve X
) : exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X), R = Sieve.
ofArrows _ f
· 使用定理 `CategoryTheory.Sieve.ofArrows.eq_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {I : Type u_1} {X : C} (Y : I → C) (f : (i : I) → Y i ⟶ 
X),   CategoryTheory.Sie…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_map_eq_functorPushforward`：generate_map_eq
_functorPushforward {s : Presieve X} : generate (s.map F) = (generate s).functor
Pushforward F
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf_type`：op_comp_isSheaf_
of_isSheaf_type [F.IsContinuous J K] {G : Dᵒᵖ ⥤ Type*} (h : Presieve.IsSheaf K G
) : Presieve.IsSheaf J (F.op ⋙ G)
· 使用定理 `CategoryTheory.classifier_isSheaf`：classifier_isSheaf : Presieve.IsSheaf
 J₁ (Functor.closedSieves J₁).toFunctor
· 使用定理 `CategoryTheory.Presieve.isSheafFor_arrows_iff`：isSheafFor_arrows_iff : (
ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I) -> P.obj (op (X i))), Arrows.C
ompatible P π x -> exists! t, foral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Continuous functors send covering sieves to covering sieves.
The converse is false, see [SGA4, III, Exemple 1.9.3][sga-4-tome-1].
-/
lemma CoverPreserving.of_isContinuous [F.IsContinuous J K] : CoverPreserving J K F where
  cover_preserve {X S} hS := by
    rw [K.mem_iff_isSheafFor_closedSieves]
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.ofArrows, ← Sieve.generate_map_eq_functorPushforward,
      ← Presieve.isSheafFor_iff_generate, Presieve.map_ofArrows]
    have := Functor.op_comp_isSheaf_of_isSheaf_type F J (classifier_isSheaf K) _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate] at this
    rw [Presieve.isSheafFor_arrows_iff] at this ⊢
    intro x hx
    refine this x fun i j Z gi gj hgij ↦ hx _ _ _ _ _ ?_
    simp [← Functor.map_comp, hgij]

/-- If `F` is flat, it is continuous if and only if it preserves covers. -/
/-
**CategoryTheory.Functor.isContinuous_iff_coverPreserving** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {J : CategoryTheory.GrothendieckTopology C}   {K : CategoryTheory.GrothendieckT
opology D} [CategoryTheory.RepresentablyFlat F],   F.IsContinuous J K ↔ Category
Theory.CoverPreserving J K F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CoverPreserving.of_isContinuous`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isContinuous_of_coverPreserving`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.compatiblePreservingOfFlat`：compatiblePreservingOfFlat {C
 : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (K : GrothendieckT
opology D) (G : C ⥤ D) [Represe…

--- 原说明 ---
If `F` is flat, it is continuous if and only if it preserves covers.
-/
lemma Functor.isContinuous_iff_coverPreserving [RepresentablyFlat F] :
    F.IsContinuous J K ↔ CoverPreserving J K F := by
  refine ⟨fun h ↦ .of_isContinuous _ _ _, fun h ↦ ?_⟩
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `C` has pullbacks and `F : C ⥤ D` preserves pullbacks, any cover preserving
functor preserves all `1`-hypercovers. -/
/-
**CategoryTheory.Functor.PreservesOneHypercovers.of_coverPreserving** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesOneHypercovers`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {J : CategoryTheory.GrothendieckTopology C}   {K : CategoryTheory.GrothendieckT
opology D} [CategoryTheory.Limits.HasPullbacks C]   [CategoryTheory.Limits.Prese
rvesLimitsOfShape CategoryTheory.Limits.WalkingCospan F],   CategoryTheory.Cover
Preserving J K F → F.PreservesOneHypercovers J K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreZeroHypercover.sieve₀_map`：sieve₀_map : (E.map F).siev
e₀ = E.sieve₀.functorPushforward F
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₀`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S), s…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (E
 : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfArrowsOfHasPullback`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) {ι : Ty
pe u_1} (Z : ι → C)   (g : (i : ι) → Z i ⟶ X) [∀ (i…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `CategoryTheory.Limits.hasPullback_of_preservesPullback`：hasPullback_of_p
reservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g)
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₁`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S) (i…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.PreOneHypercover.pullback_sieve₁`：pullback_sieve₁ {i₁ i₂ 
: E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂) {T : C} (f : T ⟶ W) : Sieve.
pullback f (E.sieve₁ p₁ p₂) = E.sieve…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用引理 `CategoryTheory.PreOneHypercover.functorPushforward_sieve₁_of_preservesPu
llbacks`：functorPushforward_sieve₁_of_preservesPullbacks (h : p₁ ≫ E.f _ = p₂ ≫ 
E.f _) [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] : Si…

--- 原说明 ---
If `C` has pullbacks and `F : C ⥤ D` preserves pullbacks, any cover preserving
functor preserves all `1`-hypercovers.
-/
lemma Functor.PreservesOneHypercovers.of_coverPreserving [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F] (H : CoverPreserving J K F) :
    Functor.PreservesOneHypercovers.{w} F J K := by
  refine fun {U} E ↦ ⟨?_, fun i₁ i₂ W p₁ p₂ h ↦ ?_⟩
  · simp [PreZeroHypercover.sieve₀_map, H.cover_preserve E.mem₀]
  · let P : C := pullback (E.f i₁) (E.f i₂)
    have : HasPullback ((E.toPreOneHypercover.map F).f i₁) ((E.toPreOneHypercover.map F).f i₂) :=
      hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
    have := H.cover_preserve (E.mem₁ i₁ i₂ (pullback.fst (E.f i₁) (E.f i₂)) _ pullback.condition)
    rw [PreOneHypercover.functorPushforward_sieve₁_of_preservesPullbacks _ _ _
      pullback.condition] at this
    refine K.superset_covering ?_
      (K.pullback_stable (IsPullback.lift (.map _ (.of_hasPullback _ _)) p₁ p₂ h) this)
    simp [PreOneHypercover.pullback_sieve₁]

end CategoryTheory

