/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Preservation and reflection of monomorphisms and epimorphisms

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/

@[expose] public section


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

to_dual_name_hint Left Right

/-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
/-
**CategoryTheory.Functor.PreservesMonomorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves monomorphisms if it maps monomorphisms to monomorphisms.
-/
class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
@[to_dual]
/-
**CategoryTheory.Functor.PreservesEpimorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves epimorphisms if it maps epimorphisms to epimorphisms.
-/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

@[to_dual]
/-
**CategoryTheory.Functor.map_epi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f
] : Epi (F.map f)
参数：F : C ⥤ D；f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesEpimorphisms.preserves`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
monomorphisms. -/
/-
**CategoryTheory.Functor.ReflectsMonomorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor reflects monomorphisms if morphisms that are mapped to monomorphisms a
re themselves
monomorphisms.
-/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
  monomorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
epimorphisms. -/
@[to_dual]
/-
**CategoryTheory.Functor.ReflectsEpimorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are
 themselves
epimorphisms.
-/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
  epimorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f

@[to_dual]
/-
**CategoryTheory.Functor.epi_of_epi_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y} 
(h : Epi (F.map f)) : Epi f
参数：F : C ⥤ D；h : Epi (F.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsEpimorphisms.reflects`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory
.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h

@[to_dual]
/-
**CategoryTheory.Functor.preservesMonomorphisms_comp** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphism
s F] [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G) where preserves
 f h
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
-/
instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    exact inferInstance

@[to_dual]
/-
**CategoryTheory.Functor.reflectsMonomorphisms_comp** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms 
F] [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G) where reflects _ h
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
-/
instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G) where
  reflects _ h := F.mono_of_mono_map (G.mono_of_mono_map h)

@[to_dual]
/-
**CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E) [Pr
eservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
-/
theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun f _ => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩

@[to_dual]
/-
**CategoryTheory.Functor.reflectsEpimorphisms_of_preserves_of_reflects** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E) [Pre
servesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
-/
theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun f _ => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩

@[to_dual]
/-
**CategoryTheory.Functor.PreservesMonomorphisms.of_natTrans** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.PreservesMonomorphisms`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} [F.PreservesMonomorphisms] (f : G ⟶ F) [∀ (X : C), CategoryTheory.Mono (f.app
 X)],   G.PreservesMonomorphisms
参数：f : G ⟶ F；X : C；f.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
-/
lemma PreservesMonomorphisms.of_natTrans {F G : C ⥤ D} [PreservesMonomorphisms F]
    (f : G ⟶ F) [∀ X, Mono (f.app X)] :
    PreservesMonomorphisms G where
  preserves {X Y} π hπ := by
    suffices Mono (G.map π ≫ f.app Y) from mono_of_mono (G.map π) (f.app Y)
    rw [f.naturality π]
    infer_instance

@[to_dual]
/-
**CategoryTheory.Functor.PreservesMonomorphisms.of_iso** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.PreservesMonomorphisms`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} [F.PreservesMonomorphisms] (α : F ≅ G), G.PreservesMonomorphisms
参数：α : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesMonomorphisms.of_natTrans`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
-/
theorem PreservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  of_natTrans α.inv

@[to_dual]
/-
**CategoryTheory.Functor.PreservesMonomorphisms.iso_iff** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.PreservesMonomorphisms`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G), F.PreservesMonomorphisms ↔ G.PreservesMonomorphisms
参数：α : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesMonomorphisms.of_iso`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   {F G : CategoryThe…
-/
theorem PreservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[to_dual]
/-
**CategoryTheory.Functor.ReflectsMonomorphisms.of_iso** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor.ReflectsMonomorphisms`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} [F.ReflectsMonomorphisms] (α : F ≅ G), G.ReflectsMonomorphisms
参数：α : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ReflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G where
  reflects {X Y} f h := by
    apply F.mono_of_mono_map
    suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
    simp

@[to_dual]
/-
**CategoryTheory.Functor.ReflectsMonomorphisms.iso_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.ReflectsMonomorphisms`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G), F.ReflectsMonomorphisms ↔ G.ReflectsMonomorphisms
参数：α : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsMonomorphisms.of_iso`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F G : CategoryThe…
-/
theorem ReflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_natTrans := PreservesMonomorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_iso := PreservesMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.iso_iff := PreservesMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.of_iso := ReflectsMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.iso_iff := ReflectsMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_natTrans := PreservesEpimorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_iso := PreservesEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.iso_iff := PreservesEpimorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.of_iso := ReflectsEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.iso_iff := ReflectsEpimorphisms.iso_iff

@[to_dual]
/-
**CategoryTheory.Functor.preservesEpimorphisms_of_adjunction** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesEpimorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) 
: PreservesEpimorphisms F where preserves {X Y} f hf
参数：adj : F ⊣ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
-/
theorem preservesEpimorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F where
  preserves {X Y} f hf := ⟨by
    intro Z g h H
    replace H := congr_arg (adj.homEquiv X Z) H
    rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
      Equiv.apply_eq_iff_eq] at H⟩

@[to_dual]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preservesEpimorphisms_of_adjunction (Adjunction.ofIsLeftAdjoint F)

@[to_dual]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F where
  reflects {X} {Y} f _ :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩

@[to_dual]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : C ⥤ D} (f : F ⟶ G) [IsSplitEpi f] (X : C) : IsSplitEpi (f.app X) :=
  inferInstanceAs (IsSplitEpi (((evaluation C D).obj X).map f))

@[to_dual]
/-
**CategoryTheory.Functor.PreservesEpimorphisms.ofRetract** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor.PreservesEpimorphisms`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (r : CategoryTheory.Retract G F) [F.PreservesEpimorphisms], G.PreservesEpimor
phisms
参数：r : CategoryTheory.Retract G F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesEpimorphisms.preserves`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.PreservesEpimorphisms.of_natTrans`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.Functor.instIsSplitEpiApp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Retract.instIsSplitEpiR`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Retract X Y),   CategoryT
heory.IsSplitEpi h.r
-/
lemma PreservesEpimorphisms.ofRetract {F G : C ⥤ D} (r : Retract G F) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves := (PreservesEpimorphisms.of_natTrans r.r).preserves

@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.ofRetract := PreservesEpimorphisms.ofRetract
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.ofRetract := PreservesMonomorphisms.ofRetract

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
@[to_dual
/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/]
/-
**CategoryTheory.Functor.splitEpiEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f) wher
e toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f) where
  toFun f := f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by cat_disch
  right_inv x := by cat_disch

@[to_dual (attr := simp)]
/-
**CategoryTheory.Functor.isSplitEpi_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `CategoryTheory.IsSplitEpi.exists_splitEpi`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsSp
litEpi f],   Nonempty (Category…
-/
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)

@[to_dual (attr := simp)]
/-
**CategoryTheory.Functor.epi_map_iff_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphism
s F] : Epi (F.map f) ↔ Epi f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
-/
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `SplitEpiCategory`,
then `D` also is. -/
@[to_dual
/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `SplitMonoCategory`,
then `D` also is. -/]
/-
**CategoryTheory.Functor.splitEpiCategoryImpOfIsEquivalence** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] 
: SplitEpiCategory D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.isSplitEpi_iff`：isSplitEpi_iff [Full F] [Faithful
 F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

@[to_dual]
/-
**CategoryTheory.Adjunction.strongEpi_map_of_strongEpi** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [F'.PreservesMonomor
phisms] [F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f)
参数：adj : F ⊣ F'；f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.hasLiftingProperty_iff`：hasLiftingProperty_iff
 (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) : HasLiftingProperty 
(G.map i) p ↔ HasLiftingProperty i (F.…
· 使用定理 `CategoryTheory.StrongEpi.llp`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f]   ⦃X Y 
: C⦄ (z : X ⟶ Y) […
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
-/
theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [F'.PreservesMonomorphisms]
    [F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.hasLiftingProperty_iff]
    infer_instance⟩

@[to_dual]
/-
**CategoryTheory.Adjunction.strongEpi_map_of_isEquivalence** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Adjunction`。
形式化陈述：strongEpi_map_of_isEquivalence [F.IsEquivalence] (f : A ⟶ B) [_h : StrongE
pi f] : StrongEpi (F.map f)
参数：f : A ⟶ B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.strongEpi_map_of_strongEpi`：strongEpi_map_of_s
trongEpi (adj : F ⊣ F') (f : A ⟶ B) [F'.PreservesMonomorphisms] [F.PreservesEpim
orphisms] [StrongEpi f] : StrongEpi (F.map…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance strongEpi_map_of_isEquivalence [F.IsEquivalence] (f : A ⟶ B) [_h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f

@[to_dual]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (adj : F ⊣ F') {X : C} {Y : D} (f : F.obj X ⟶ Y) [hf : Mono f] [F.ReflectsMonomorphisms] :
    Mono (adj.homEquiv _ _ f) :=
  F.mono_of_mono_map <| by
    rw [← (homEquiv adj X Y).symm_apply_apply f] at hf
    exact mono_of_mono_fac (adj.homEquiv_counit _ _ _).symm

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[to_dual (attr := simp)]
/-
**CategoryTheory.Functor.strongEpi_map_iff_strongEpi_of_isEquivalence** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] : StrongEpi
 (F.map f) ↔ StrongEpi f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.StrongEpi.iff_of_arrow_iso`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}   (e : Cat
egoryTheory.Arrow.mk f ≅ Catego…
-/
theorem strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] :
    StrongEpi (F.map f) ↔ StrongEpi f := by
  constructor
  · intro
    have e : Arrow.mk f ≅ Arrow.mk (F.inv.map (F.map f)) :=
      Arrow.isoOfNatIso F.asEquivalence.unitIso (Arrow.mk f)
    rw [StrongEpi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance

end CategoryTheory.Functor

