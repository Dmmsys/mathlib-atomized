/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Mario Carneiro, Reid Barton, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Topology.Sheaves.Init

/-!
# Presheaves on a topological space

We define `TopCat.Presheaf C X` simply as `(TopologicalSpace.Opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* Given `{X Y : TopCat.{w}}` and `f : X ⟶ Y`, we define
  `TopCat.Presheaf.pushforward C f : X.Presheaf C ⥤ Y.Presheaf C`,
  with notation `f _* ℱ` for `ℱ : X.Presheaf C`.

and for `ℱ : X.Presheaf C` provide the natural isomorphisms
* `TopCat.Presheaf.Pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `TopCat.Presheaf.Pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
  along with their `@[simp]` lemmas.

We also define the functors `pullback C f : Y.Presheaf C ⥤ X.Presheaf c`,
and provide their adjunction at
`TopCat.Presheaf.pullbackPushforwardAdjunction`.
-/

@[expose] public section

universe w v u

open CategoryTheory TopologicalSpace Opposite Functor

variable (C : Type u) [Category.{v} C]

namespace TopCat

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[implicit_reducible]
/-
**TopCat.Presheaf** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：Presheaf (X : TopCat.{w}) : Type max u v w
参数：X : TopCat.{w}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `C`-valued presheaves on a (bundled) topological space `X`.
-/
def Presheaf (X : TopCat.{w}) : Type max u v w :=
  (Opens X)ᵒᵖ ⥤ C
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : TopCat.{w}) : Category (Presheaf.{w, v, u} C X) :=
  inferInstanceAs (Category ((Opens X)ᵒᵖ ⥤ C : Type max u v w))

variable {C}

namespace Presheaf

/-
**TopCat.Presheaf.comp_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : TopCat} {U :
 (TopologicalSpace.Opens ↑X)ᵒᵖ}   {P Q R : TopCat.Presheaf C X} (f : P ⟶ Q) (g :
 Q ⟶ R),   (CategoryTheory.CategoryStruct.comp f g).app U = CategoryTheory.Categ
oryStruct.comp (f.app U) (g.app U)
参数：TopologicalSpace.Opens ↑X；f : P ⟶ Q；g : Q ⟶ R；CategoryTheory.CategoryStruct.c
omp f g；f.app U；g.app U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem comp_app {X : TopCat.{w}} {U : (Opens X)ᵒᵖ} {P Q R : Presheaf C X}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).app U = f.app U ≫ g.app U := rfl

@[ext]
/-
**TopCat.Presheaf.ext** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P ⟶ Q} (w : forall U : Op
ens X, f.app (op U) = g.app (op U)) : f = g
参数：w : forall U : Opens X, f.app (op U) = g.app (op U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P ⟶ Q}
    (w : ∀ U : Opens X, f.app (op U) = g.app (op U)) :
    f = g := by
  apply NatTrans.ext
  ext U
  induction U with | _ U => ?_
  apply w

/-- attribute `sheaf_restrict` to mark lemmas related to restricting sheaves -/
macro "sheaf_restrict" : attr =>
  `(attr|aesop safe 50 apply (rule_sets := [$(Lean.mkIdent `Restrict):ident]))

attribute [sheaf_restrict] bot_le le_top le_refl inf_le_left inf_le_right
  le_sup_left le_sup_right

/-- `restrict_tac` solves relations among subsets (copied from `aesop cat`) -/
macro (name := restrict_tac) "restrict_tac" c:Aesop.tactic_clause* : tactic =>
`(tactic| first | assumption |
  aesop $c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false })
    (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

/-- `restrict_tac?` passes along `Try this` from `aesop` -/
macro (name := restrict_tac?) "restrict_tac?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false
                 maxRuleApplications := 300 })
  (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

attribute [aesop 10% (rule_sets := [Restrict])] le_trans
attribute [aesop safe destruct (rule_sets := [Restrict])] Eq.trans_le
attribute [aesop safe -50 (rule_sets := [Restrict])] Aesop.BuiltinRules.assumption

/-
**TopCat.Presheaf.** 是 Mathlib 中的一个示例，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {X} [CompleteLattice X] (v : Nat → X) (w x y z : X) (e : v 0 = v 1) (_ : v 1 = v 2)
    (h₀ : v 1 ≤ x) (_ : x ≤ z ⊓ w) (h₂ : x ≤ y ⊓ z) : v 0 ≤ y := by
  restrict_tac

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ₕ i` (`h` stands for `hom`) for `i : U ⟶ V`,
and the notation `x |_ₗ U ⟪i⟫` (`l` stands for `le`) for `i : U ≤ V`.
-/
/-
**TopCat.Presheaf.restrict** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：restrict {F : X.Presheaf C} {V : Opens X} (x : ToType (F.obj (op V))) {U :
 Opens X} (h : U ⟶ V) : ToType (F.obj (op U))
参数：x : ToType (F.obj (op V))；h : U ⟶ V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ₕ i` (`h` stands for `hom`)
 for `i : U ⟶ V`,
and the notation `x |_ₗ U ⟪i⟫` (`l` stands for `le`) for `i : U ≤ V`.
-/
def restrict {F : X.Presheaf C}
    {V : Opens X} (x : ToType (F.obj (op V))) {U : Opens X} (h : U ⟶ V) : ToType (F.obj (op U)) :=
  F.map h.op x

/-- restriction of a section along an inclusion -/
scoped[AlgebraicGeometry] infixl:80 " |_ₕ " => TopCat.Presheaf.restrict
/-- restriction of a section along a subset relation -/
scoped[AlgebraicGeometry] notation:80 x " |_ₗ " U " ⟪" e "⟫ " =>
  @TopCat.Presheaf.restrict _ _ _ _ _ _ _ _ _ x U (@homOfLE (Opens _) _ U _ e)

open AlgebraicGeometry

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ U`, where the proof `U ≤ V` is inferred by
the tactic `Top.presheaf.restrict_tac'` -/
/-
**TopCat.Presheaf.restrictOpen** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：restrictOpen {F : X.Presheaf C} {V : Opens X} (x : ToType (F.obj (op V))) 
(U : Opens X) (e : U <= V
参数：x : ToType (F.obj (op V))；U : Opens X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ U`, where the proof `U ≤ V
` is inferred by
the tactic `Top.presheaf.restrict_tac'`
-/
abbrev restrictOpen {F : X.Presheaf C}
    {V : Opens X} (x : ToType (F.obj (op V))) (U : Opens X)
    (e : U ≤ V := by restrict_tac) :
    ToType (F.obj (op U)) :=
  x |_ₗ U ⟪e⟫

/-- restriction of a section to open subset -/
scoped[AlgebraicGeometry] infixl:80 " |_ " => TopCat.Presheaf.restrictOpen

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.Presheaf.restrict_restrict** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：restrict_restrict {F : X.Presheaf C} {U V W : Opens X} (e₁ : U <= V) (e₂ :
 V <= W) (x : ToType (F.obj (op W))) : x |_ V |_ U = x |_ U
参数：e₁ : U <= V；e₂ : V <= W；x : ToType (F.obj (op W))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem restrict_restrict
    {F : X.Presheaf C} {U V W : Opens X} (e₁ : U ≤ V) (e₂ : V ≤ W) (x : ToType (F.obj (op W))) :
    x |_ V |_ U = x |_ U := by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.Presheaf.map_restrict** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：map_restrict {F G : X.Presheaf C} (e : F ⟶ G) {U V : Opens X} (h : U <= V)
 (x : ToType (F.obj (op V))) : e.app _ (x |_ U) = e.app _ x |_ U
参数：e : F ⟶ G；h : U <= V；x : ToType (F.obj (op V))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem map_restrict
    {F G : X.Presheaf C} (e : F ⟶ G) {U V : Opens X} (h : U ≤ V) (x : ToType (F.obj (op V))) :
    e.app _ (x |_ U) = e.app _ x |_ U := by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply, NatTrans.naturality, ConcreteCategory.comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**TopCat.Presheaf.restrict_self** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：restrict_self {F : X.Presheaf C} {U : Opens X} (x : ToType (F.obj (op U)))
 : x |_ U = x
参数：x : ToType (F.obj (op U))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_self {F : X.Presheaf C} {U : Opens X} (x : ToType (F.obj (op U))) :
    x |_ U = x := by
  simp [restrictOpen, restrict]

open CategoryTheory.Limits

variable (C)

/-- The pushforward functor. -/
@[simps!, implicit_reducible]
/-
**TopCat.Presheaf.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：pushforward {X Y : TopCat.{w}} (f : X ⟶ Y) : X.Presheaf C ⥤ Y.Presheaf C
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward functor.
-/
def pushforward {X Y : TopCat.{w}} (f : X ⟶ Y) : X.Presheaf C ⥤ Y.Presheaf C :=
  (whiskeringLeft _ _ _).obj (Opens.map f).op

/-- push forward of a presheaf -/
scoped[AlgebraicGeometry] notation f:80 " _* " P:81 =>
  Functor.obj (TopCat.Presheaf.pushforward _ f) P

@[simp]
/-
**TopCat.Presheaf.pushforward_map_app'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshea
f`。
形式化陈述：pushforward_map_app' {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (
α : ℱ ⟶ 𝒢) {U : (Opens Y)ᵒᵖ} : ((pushforward C f).map α).app U = α.app (op <| (O
pens.map f).obj U.unop)
参数：f : X ⟶ Y；α : ℱ ⟶ 𝒢；Opens Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushforward_map_app' {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢)
    {U : (Opens Y)ᵒᵖ} : ((pushforward C f).map α).app U = α.app (op <| (Opens.map f).obj U.unop) :=
  rfl
/-
**TopCat.Presheaf.id_pushforward** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：id_pushforward (X : TopCat.{w}) : pushforward C (𝟙 X) = 𝟭 (X.Presheaf C)
参数：X : TopCat.{w}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_pushforward (X : TopCat.{w}) : pushforward C (𝟙 X) = 𝟭 (X.Presheaf C) := rfl

variable {C}

namespace Pushforward

/-- The natural isomorphism between the pushforward of a presheaf along the identity continuous map
and the original presheaf. -/
/-
**TopCat.Presheaf.Pushforward.id** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf.Push
forward`。
形式化陈述：id {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ ≅ ℱ
参数：ℱ : X.Presheaf C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the pushforward of a presheaf along the identity
 continuous map
and the original presheaf.
-/
def id {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ ≅ ℱ := Iso.refl _

@[simp]
/-
**TopCat.Presheaf.Pushforward.id_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presh
eaf.Pushforward`。
形式化陈述：id_hom_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) : (id ℱ).hom.app U = 𝟙 
_
参数：ℱ : X.Presheaf C；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) : (id ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
/-
**TopCat.Presheaf.Pushforward.id_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presh
eaf.Pushforward`。
形式化陈述：id_inv_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) : (id ℱ).inv.app U = 𝟙 
_
参数：ℱ : X.Presheaf C；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_inv_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) :
    (id ℱ).inv.app U = 𝟙 _ := rfl
/-
**TopCat.Presheaf.Pushforward.id_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf.P
ushforward`。
形式化陈述：id_eq {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ = ℱ
参数：ℱ : X.Presheaf C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ = ℱ := rfl

/-- The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
/-
**TopCat.Presheaf.Pushforward.comp** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf.Pu
shforward`。
形式化陈述：comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) : (f 
≫ g) _* ℱ ≅ g _* (f _* ℱ)
参数：f : X ⟶ Y；g : Y ⟶ Z；ℱ : X.Presheaf C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward.
-/
def comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
    (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) := Iso.refl _
/-
**TopCat.Presheaf.Pushforward.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf
.Pushforward`。
形式化陈述：comp_eq {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) : 
(f ≫ g) _* ℱ = g _* (f _* ℱ)
参数：f : X ⟶ Y；g : Y ⟶ Z；ℱ : X.Presheaf C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
    (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl

@[simp]
/-
**TopCat.Presheaf.Pushforward.comp_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pre
sheaf.Pushforward`。
形式化陈述：comp_hom_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf 
C) (U) : (comp f g ℱ).hom.app U = 𝟙 _
参数：f : X ⟶ Y；g : Y ⟶ Z；ℱ : X.Presheaf C；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U) :
    (comp f g ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
/-
**TopCat.Presheaf.Pushforward.comp_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pre
sheaf.Pushforward`。
形式化陈述：comp_inv_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf 
C) (U) : (comp f g ℱ).inv.app U = 𝟙 _
参数：f : X ⟶ Y；g : Y ⟶ Z；ℱ : X.Presheaf C；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_inv_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U) :
    (comp f g ℱ).inv.app U = 𝟙 _ := rfl

end Pushforward

/--
An equality of continuous maps induces a natural isomorphism between the pushforwards of a presheaf
along those maps.
-/
/-
**TopCat.Presheaf.pushforwardEq** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：pushforwardEq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf
 C) : f _* ℱ ≅ g _* ℱ
参数：h : f = g；ℱ : X.Presheaf C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality of continuous maps induces a natural isomorphism between the pushfor
wards of a presheaf
along those maps.
-/
def pushforwardEq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ ≅ g _* ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ
/-
**TopCat.Presheaf.pushforward_eq'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：pushforward_eq' {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Preshe
af C) : f _* ℱ = g _* ℱ
参数：h : f = g；ℱ : X.Presheaf C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem pushforward_eq' {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ = g _* ℱ := by rw [h]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**TopCat.Presheaf.pushforwardEq_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：pushforwardEq_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.
Presheaf C) (U) : (pushforwardEq h ℱ).hom.app U = ℱ.map (eqToHom (by cat_disch))
参数：h : f = g；ℱ : X.Presheaf C；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushforwardEq_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (h : f = g) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq h ℱ).hom.app U = ℱ.map (eqToHom (by cat_disch)) := by
  simp [pushforwardEq]

variable (C)

section Iso

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps!]
/-
**TopCat.Presheaf.presheafEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：presheafEquivOfIso {X Y : TopCat.{w}} (H : X ≅ Y) : X.Presheaf C ≌ Y.Presh
eaf C
参数：H : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism of spaces gives an equivalence of categories of presheaves.
-/
def presheafEquivOfIso {X Y : TopCat.{w}} (H : X ≅ Y) : X.Presheaf C ≌ Y.Presheaf C :=
  Equivalence.congrLeft (Opens.mapMapIso H).symm.op

variable {C}

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
/-
**TopCat.Presheaf.toPushforwardOfIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：toPushforwardOfIso {X Y : TopCat.{w}} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : 
Y.Presheaf C} (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢
参数：H : X ≅ Y；α : H.hom _* ℱ ⟶ 𝒢。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def toPushforwardOfIso {X Y : TopCat.{w}} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
  (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**TopCat.Presheaf.toPushforwardOfIso_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presh
eaf`。
形式化陈述：toPushforwardOfIso_app {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} 
{𝒢 : Y.Presheaf C} (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : (Opens X)ᵒᵖ) : (toPushforwardOfIs
o H₁ H₂).app U = ℱ.map (eqToHom (by simp [Opens.map_def, Set.preimage_preimage])
) ≫ H₂.app (op ((Opens.map H₁.inv).obj (unop U)))
参数：H₁ : X ≅ Y；H₂ : H₁.hom _* ℱ ⟶ 𝒢；U : (Opens X)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `TopCat.Presheaf.presheafEquivOfIso_unitIso_hom_app_app`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] {X Y : TopCat} (H : X ≅ Y)   (X_1 : Cat
egoryTheory.Functor (TopologicalSpace.Opens …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toPushforwardOfIso_app {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : (Opens X)ᵒᵖ) :
    (toPushforwardOfIso H₁ H₂).app U =
      ℱ.map (eqToHom (by simp [Opens.map_def, Set.preimage_preimage])) ≫
        H₂.app (op ((Opens.map H₁.inv).obj (unop U))) := by
  simp [toPushforwardOfIso, Adjunction.homEquiv_unit]

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
/-
**TopCat.Presheaf.pushforwardToOfIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：pushforwardToOfIso {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 :
 X.Presheaf C} (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢
参数：H₁ : X ≅ Y；H₂ : ℱ ⟶ H₁.hom _* 𝒢。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforwardToOfIso {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
  ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**TopCat.Presheaf.pushforwardToOfIso_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presh
eaf`。
形式化陈述：pushforwardToOfIso_app {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} 
{𝒢 : X.Presheaf C} (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : (Opens X)ᵒᵖ) : (pushforwardToOfIs
o H₁ H₂).app U = H₂.app (op ((Opens.map H₁.inv).obj (unop U))) ≫ 𝒢.map (eqToHom 
(by simp [Opens.map_def, Set.preimage_preimage]))
参数：H₁ : X ≅ Y；H₂ : ℱ ⟶ H₁.hom _* 𝒢；U : (Opens X)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `TopCat.Presheaf.presheafEquivOfIso_counitIso_hom_app_app`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C] {X Y : TopCat} (H : X ≅ Y)   (X_1 : C
ategoryTheory.Functor (TopologicalSpace.Opens …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushforwardToOfIso_app {X Y : TopCat.{w}} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : (Opens X)ᵒᵖ) :
    (pushforwardToOfIso H₁ H₂).app U =
      H₂.app (op ((Opens.map H₁.inv).obj (unop U))) ≫
        𝒢.map (eqToHom (by simp [Opens.map_def, Set.preimage_preimage])) := by
  simp [pushforwardToOfIso, Equivalence.toAdjunction, Adjunction.homEquiv_counit]

end Iso

variable [HasColimits C]

noncomputable section

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `X`. -/
/-
**TopCat.Presheaf.pullback** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：pullback {X Y : TopCat.{v}} (f : X ⟶ Y) : Y.Presheaf C ⥤ X.Presheaf C
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presh
eaf
on `X`.
-/
def pullback {X Y : TopCat.{v}} (f : X ⟶ Y) : Y.Presheaf C ⥤ X.Presheaf C :=
  (Opens.map f).op.lan

/-- The pullback and pushforward along a continuous map are adjoint to each other. -/
/-
**TopCat.Presheaf.pullbackPushforwardAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `TopCa
t.Presheaf`。
形式化陈述：pullbackPushforwardAdjunction {X Y : TopCat.{v}} (f : X ⟶ Y) : pullback C 
f ⊣ pushforward C f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback and pushforward along a continuous map are adjoint to each other.
-/
def pullbackPushforwardAdjunction {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullback C f ⊣ pushforward C f :=
  Functor.lanAdjunction _ _

@[deprecated (since := "2026-03-03")]
alias pushforwardPullbackAdjunction := pullbackPushforwardAdjunction

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
/-
**TopCat.Presheaf.pullbackHomIsoPushforwardInv** 是 Mathlib 中的一个定义，位于命名空间 `TopCat
.Presheaf`。
形式化陈述：pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) : pullback C H
.hom ≅ pushforward C H.inv
参数：H : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back along a homeomorphism is the same as pushing forward along its inve
rse.
-/
def pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.hom)
    (presheafEquivOfIso C H.symm).toAdjunction

/-- Pulling back along the inverse of a homeomorphism is the same as pushing forward along it. -/
/-
**TopCat.Presheaf.pullbackInvIsoPushforwardHom** 是 Mathlib 中的一个定义，位于命名空间 `TopCat
.Presheaf`。
形式化陈述：pullbackInvIsoPushforwardHom {X Y : TopCat.{v}} (H : X ≅ Y) : pullback C H
.inv ≅ pushforward C H.hom
参数：H : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back along the inverse of a homeomorphism is the same as pushing forward
 along it.
-/
def pullbackInvIsoPushforwardHom {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.inv ≅ pushforward C H.hom :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.inv)
    (presheafEquivOfIso C H).toAdjunction

variable {C}

/-- If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`. -/
/-
**TopCat.Presheaf.pullbackObjObjOfImageOpen** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Pr
esheaf`。
形式化陈述：pullbackObjObjOfImageOpen {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C
) (U : Opens X) (H : IsOpen (f '' U)) : ((pullback C f).obj ℱ).obj (op U) ≅ ℱ.ob
j (op ⟨_, H⟩)
参数：f : X ⟶ Y；ℱ : Y.Presheaf C；U : Opens X；H : IsOpen (f '' U)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`.
-/
def pullbackObjObjOfImageOpen {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X)
    (H : IsOpen (f '' U)) : ((pullback C f).obj ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) := by
  let x : CostructuredArrow (Opens.map f).op (op U) := CostructuredArrow.mk
    (@homOfLE _ _ _ ((Opens.map f).obj ⟨_, H⟩) (Set.image_preimage.le_u_l _)).op
  have hx : IsTerminal x :=
    { lift := fun s ↦ by
        fapply CostructuredArrow.homMk
        · change op (unop _) ⟶ op (⟨_, H⟩ : Opens _)
          refine (homOfLE ?_).op
          apply (Set.image_mono s.pt.hom.unop.le).trans
          exact Set.image_preimage.l_u_le (SetLike.coe s.pt.left.unop)
        · simp [eq_iff_true_of_subsingleton] }
  exact IsColimit.coconePointUniqueUpToIso
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U))
    (colimitOfDiagramTerminal hx _)

set_option backward.isDefEq.respectTransparency false in
/-- If `U ⊆ V` and `f '' U`, `f '' V` are open, then the isomorphisms `f⁻¹ℱ U ≅ ℱ (f '' U)`,
`f⁻¹ℱ V ≅ ℱ (f '' V)` given by `pullbackObjObjOfImageOpen` are compatible with the restriction
maps. -/
/-
**TopCat.Presheaf.pullbackObjObjOfImageOpen_hom_naturality** 是 Mathlib 中的一个定理，位于
命名空间 `TopCat.Presheaf`。
形式化陈述：pullbackObjObjOfImageOpen_hom_naturality {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ
 : Y.Presheaf C) {U V : Opens X} (HU : IsOpen (f '' U)) (HV : IsOpen (f '' V)) (
le : U <= V) : ((pullback C f).obj ℱ).map (homOfLE le).op ≫ (pullbackObjObjOfIma
geOpen f ℱ U HU).hom = (pullbackObjObjOfImageOpen f ℱ V HV).hom ≫ ℱ.map (IsOpenM
ap.functorMap HU HV le).op
参数：f : X ⟶ Y；ℱ : Y.Presheaf C；HU : IsOpen (f '' U)；HV : IsOpen (f '' V)；le : U <
= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.LeftExtension.coconeAt_ι_app`：∀ {C : Type u_1} {D
 : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [ins
t_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.LeftExtension.mk_hom`：∀ {C : Type u_1} {H : Type 
u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc`
：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst
_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.coconeOfDiagramTerminal_ι_app`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {J : Type u} [inst_1 : CategoryTheory.C
ategory.{v, u} J]   {X : J} (tX : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `U ⊆ V` and `f '' U`, `f '' V` are open, then the isomorphisms `f⁻¹ℱ U ≅ ℱ (f
 '' U)`,
`f⁻¹ℱ V ≅ ℱ (f '' V)` given by `pullbackObjObjOfImageOpen` are compatible with t
he restriction
maps.
-/
theorem pullbackObjObjOfImageOpen_hom_naturality {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C)
    {U V : Opens X} (HU : IsOpen (f '' U)) (HV : IsOpen (f '' V)) (le : U ≤ V) :
    ((pullback C f).obj ℱ).map (homOfLE le).op ≫ (pullbackObjObjOfImageOpen f ℱ U HU).hom =
    (pullbackObjObjOfImageOpen f ℱ V HV).hom ≫ ℱ.map (IsOpenMap.functorMap HU HV le).op := by
  dsimp [pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op V)).hom_ext
    (fun j ↦ ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt
      (op V)).ι.app j ≫ ((pullback C f).obj ℱ).map (homOfLE le).op =
      ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt
      (op U)).ι.app ((CostructuredArrow.map (homOfLE le).op).obj j) := by cat_disch
  rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, reassoc_of% eq,
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom,
    Limits.coconeOfDiagramTerminal_ι_app, Limits.coconeOfDiagramTerminal_ι_app]
  dsimp
  rw [← Functor.map_comp]
  cat_disch

end

end TopCat.Presheaf

namespace IsOpenMap

noncomputable section

variable {C} [Limits.HasColimits C]

open TopCat.Presheaf

/--
If `f : X ⟶ Y` is an open map and `ℱ` is a presheaf on `Y`, then the pullback of `ℱ` by `f` is
isomorphic to the composition of `ℱ` and of the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ` induced by `f`.
-/
@[simps!]
/-
**IsOpenMap.pullbackObjIso** 是 Mathlib 中的一个定义，位于命名空间 `IsOpenMap`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasColimits C] →       {X Y : TopCat} →         {f : X ⟶ 
Y} →           (hf : IsOpenMap ⇑(CategoryTheory.ConcreteCategory.hom f)) →      
       (ℱ : TopCat.Presheaf C Y) → (TopCat.Presheaf.pullback C f).obj ℱ ≅ hf.fun
ctor.op.comp ℱ
参数：hf : IsOpenMap ⇑(CategoryTheory.ConcreteCategory.hom f)；ℱ : TopCat.Presheaf C
 Y；TopCat.Presheaf.pullback C f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` is an open map and `ℱ` is a presheaf on `Y`, then the pullback of
 `ℱ` by `f` is
isomorphic to the composition of `ℱ` and of the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ
` induced by `f`.
-/
def pullbackObjIso {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f) (ℱ : Y.Presheaf C) :
    (pullback C f).obj ℱ ≅ hf.functor.op ⋙ ℱ :=
  NatIso.ofComponents
    (fun U ↦ pullbackObjObjOfImageOpen f ℱ U.1 (hf (unop U).1 (unop U).2))
    (fun {U V} i ↦ (pullbackObjObjOfImageOpen_hom_naturality f ℱ (hf (unop V).1 (unop V).2)
      (hf (unop U).1 (unop U).2) (leOfHom i.unop)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
If `f : X ⟶ Y` is an open map, this expresses the naturality of the isomorphism
`IsOpenMap.pullbackObjIso` between the pullback by `f` of a presheaf and the composition
of that presheaf and of the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ` induced by `f`.
-/
/-
**IsOpenMap.pullbackObjIso_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasColimits C] {X Y : TopCat}   {f : X ⟶ Y} (hf : IsOpenMap ⇑(Cat
egoryTheory.ConcreteCategory.hom f)) {ℱ 𝒢 : TopCat.Presheaf C Y} (u : ℱ ⟶ 𝒢),   
CategoryTheory.CategoryStruct.comp ((TopCat.Presheaf.pullback C f).map u) (hf.pu
llbackObjIso 𝒢).hom =     CategoryTheory.CategoryStruct.comp (hf.pullbackObjIso 
ℱ).hom (hf.functor.op.whiskerLeft u)
参数：hf : IsOpenMap ⇑(CategoryTheory.ConcreteCategory.hom f)；u : ℱ ⟶ 𝒢；(TopCat.Pre
sheaf.pullback C f).map u；hf.pullbackObjIso 𝒢；hf.pullbackObjIso ℱ；hf.functor.op.
whiskerLeft u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc`
：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst
_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f : X ⟶ Y` is an open map, this expresses the naturality of the isomorphism
`IsOpenMap.pullbackObjIso` between the pullback by `f` of a presheaf and the com
position
of that presheaf and of the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ` induced by `f`.
-/
lemma pullbackObjIso_hom_naturality {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f)
   {ℱ 𝒢 : Y.Presheaf C} (u : ℱ ⟶ 𝒢) :
   (pullback C f).map u ≫ (hf.pullbackObjIso 𝒢).hom =
   (hf.pullbackObjIso ℱ).hom ≫ Functor.whiskerLeft hf.functor.op u := by
  ext U
  dsimp [pullbackObjIso, pullbackObjObjOfImageOpen]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U)).hom_ext
    (fun j ↦ ?_)
  have eq : ((LeftExtension.mk ((Opens.map f).op.leftKanExtension ℱ)
      ((Opens.map f).op.leftKanExtensionUnit ℱ)).coconeAt (op U)).ι.app j
      ≫ ((pullback C f).map u).app (op U) = NatTrans.app (Functor.whiskerLeft _ u) j ≫
      ((LeftExtension.mk ((Opens.map f).op.leftKanExtension 𝒢)
      ((Opens.map f).op.leftKanExtensionUnit 𝒢)).coconeAt (op U)).ι.app j := by
    dsimp [pullback]
    simp only [Category.assoc, NatTrans.naturality]
    have := NatTrans.congr_app ((Opens.map f).op.lanUnit.naturality u) j.left
    dsimp [lanUnit] at this
    rw [reassoc_of% this]
    rfl
  rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, reassoc_of% eq,
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom]
  dsimp
  rw [← u.naturality]
  rfl

/--
If `f : X ⟶ Y`, this is the isomorphism between the pullback functor by `f` and the
"naive" pullback given by composing presheaves with the functor `(Open X)ᵒᵖ ⥤ (Open Y)ᵒᵖ`
induced by `f`.
-/
@[simps!]
/-
**IsOpenMap.pullbackIso** 是 Mathlib 中的一个定义，位于命名空间 `IsOpenMap`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasColimits C] →       {X Y : TopCat} →         {f : X ⟶ 
Y} →           (hf : IsOpenMap ⇑(CategoryTheory.ConcreteCategory.hom f)) →      
       TopCat.Presheaf.pullback C f ≅               (CategoryTheory.Functor.whis
keringLeft (TopologicalSpace.Opens ↑X)ᵒᵖ (TopologicalSpace.Opens ↑Y)ᵒᵖ C).obj   
              hf.functor.op
参数：hf : IsOpenMap ⇑(CategoryTheory.ConcreteCategory.hom f)；CategoryTheory.Functo
r.whiskeringLeft (TopologicalSpace.Opens ↑X)ᵒᵖ (TopologicalSpace.Opens ↑Y)ᵒᵖ C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.pullbackObjIso_hom_naturality`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X Y : 
TopCat}   {f : X ⟶ Y} (hf : I…

--- 原说明 ---
If `f : X ⟶ Y`, this is the isomorphism between the pullback functor by `f` and 
the
"naive" pullback given by composing presheaves with the functor `(Open X)ᵒᵖ ⥤ (O
pen Y)ᵒᵖ`
induced by `f`.
-/
def pullbackIso {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : IsOpenMap f) :
    pullback C f ≅ (Functor.whiskeringLeft _ _ _).obj hf.functor.op :=
  NatIso.ofComponents hf.pullbackObjIso hf.pullbackObjIso_hom_naturality

end

end IsOpenMap

