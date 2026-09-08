/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of seminormed groups

We define `SemiNormedGrp`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGrp₁`, the subcategory of norm non-increasing morphisms.
-/

@[expose] public section


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
/-
**SemiNormedGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of seminormed abelian groups and bounded group homomorphisms.
-/
structure SemiNormedGrp : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp.str

namespace SemiNormedGrp

/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort SemiNormedGrp Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp` -/
@[ext]
/-
**SemiNormedGrp.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `SemiNormedGrp`。
形式化陈述：SemiNormedGrp → SemiNormedGrp → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `SemiNormedGrp`
-/
structure Hom (M N : SemiNormedGrp.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} SemiNormedGrp where
  Hom X Y := Hom X Y
  id X := ⟨NormedAddGroupHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory SemiNormedGrp (NormedAddGroupHom · ·) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `SemiNormedGrp` back into a `NormedAddGroupHom`. -/
/-
**SemiNormedGrp.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{M N : SemiNormedGrp} → M.Hom N → NormedAddGroupHom M.carrier N.carrier
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `SemiNormedGrp` back into a `NormedAddGroupHom`.
-/
abbrev Hom.hom {M N : SemiNormedGrp.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp) f

/-- Typecheck a `NormedAddGroupHom` as a morphism in `SemiNormedGrp`. -/
/-
**SemiNormedGrp.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemiNormedGrp`。
形式化陈述：ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
 (f : NormedAddGroupHom M N) : of M ⟶ of N
参数：f : NormedAddGroupHom M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `NormedAddGroupHom` as a morphism in `SemiNormedGrp`.
-/
abbrev ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) : of M ⟶ of N :=
  ConcreteCategory.ofHom (C := SemiNormedGrp) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**SemiNormedGrp.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom.Simps
`。
形式化陈述：(M N : SemiNormedGrp) → M.Hom N → NormedAddGroupHom M.carrier N.carrier
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (M N : SemiNormedGrp.{u}) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[ext]
/-
**SemiNormedGrp.ext** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : forall (x : M), f₁ x = f₂ x
) : f₁ = f₂
参数：h : forall (x : M), f₁ x = f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ConcreteCategory.ext_apply`：ext_apply {X Y : C} {f g : X 
⟶ Y} (h : forall x, f x = g x) : f = g

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

@[simp]
/-
**SemiNormedGrp.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_id {M : SemiNormedGrp} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {M : SemiNormedGrp} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/- Provided for rewriting. -/
/-
**SemiNormedGrp.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：id_apply (M : SemiNormedGrp) (r : M) : (𝟙 M : M ⟶ M) r = r
参数：M : SemiNormedGrp；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.id_apply`：∀ (V : Type u_1) [inst : SeminormedAddCommGr
oup V] (a : V), (NormedAddGroupHom.id V) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : SemiNormedGrp) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

@[simp]
/-
**SemiNormedGrp.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_comp {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) : (f ≫ g).hom = g
.hom.comp f.hom
参数：f : M ⟶ N；g : N ⟶ O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**SemiNormedGrp.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M) : (f ≫ 
g) r = g (f r)
参数：f : M ⟶ N；g : N ⟶ O；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.comp_apply`：∀ {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Ty
pe u_4} [inst : SeminormedAddCommGroup V₁]   [inst_1 : SeminormedAddCommGroup V₂
] [inst_2 : Semino…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/-
**SemiNormedGrp.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiNormedGrp.Hom.ext`：∀ {M N : SemiNormedGrp} {x y : M.Hom N}, x.hom' =
 y.hom' → x = y
-/
lemma hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**SemiNormedGrp.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGrou
p N] (f : NormedAddGroupHom M N) : (ofHom f).hom = f
参数：f : NormedAddGroupHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) : (ofHom f).hom = f := rfl

@[simp]
/-
**SemiNormedGrp.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：ofHom_hom {M N : SemiNormedGrp} (f : M ⟶ N) : ofHom (Hom.hom f) = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {M N : SemiNormedGrp} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**SemiNormedGrp.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：ofHom_id {M : Type u} [SeminormedAddCommGroup M] : ofHom (NormedAddGroupHo
m.id M) = 𝟙 (of M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {M : Type u} [SeminormedAddCommGroup M] :
    ofHom (NormedAddGroupHom.id M) = 𝟙 (of M) := rfl

@[simp]
/-
**SemiNormedGrp.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：ofHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommG
roup N] [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGro
upHom N O) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : NormedAddGroupHom M N；g : NormedAddGroupHom N O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**SemiNormedGrp.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：ofHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGr
oup N] (f : NormedAddGroupHom M N) (r : M) : ofHom f r = f r
参数：f : NormedAddGroupHom M N；r : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (r : M) : ofHom f r = f r := rfl
/-
**SemiNormedGrp.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：inv_hom_apply {M N : SemiNormedGrp} (e : M ≅ N) (r : M) : e.inv (e.hom r) 
= r
参数：e : M ≅ N；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {M N : SemiNormedGrp} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  simp
/-
**SemiNormedGrp.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_inv_apply {M N : SemiNormedGrp} (e : M ≅ N) (s : N) : e.hom (e.inv s) 
= s
参数：e : M ≅ N；s : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {M N : SemiNormedGrp} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp
/-
**SemiNormedGrp.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Typ
e u) = V
参数：V : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Type u) = V :=
  rfl
/-
**SemiNormedGrp.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：coe_id (V : SemiNormedGrp) : (𝟙 V : V -> V) = id
参数：V : SemiNormedGrp。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id (V : SemiNormedGrp) : (𝟙 V : V → V) = id :=
  rfl
/-
**SemiNormedGrp.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M -> K
) = g ∘ f
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited SemiNormedGrp :=
  ⟨of PUnit⟩
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : SemiNormedGrp} : Zero (M ⟶ N) where
  zero := ofHom 0

@[simp]
/-
**SemiNormedGrp.hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_zero {V W : SemiNormedGrp} : (0 : V ⟶ W).hom = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_zero {V W : SemiNormedGrp} : (0 : V ⟶ W).hom = 0 :=
  rfl
/-
**SemiNormedGrp.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp where
/-
**SemiNormedGrp.isZero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`
。
形式化陈述：isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZer
o V
参数：V : SemiNormedGrp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiNormedGrp.hom_ext`：hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf :
 f.hom = g.hom) : f = g
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
/-
**SemiNormedGrp.hasZeroObject** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
形式化陈述：hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiNormedGrp.isZero_of_subsingleton`：isZero_of_subsingleton (V : SemiNo
rmedGrp) [Subsingleton V] : Limits.IsZero V
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
/-
**SemiNormedGrp.iso_isometry_of_normNoninc** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormed
Grp`。
形式化陈述：iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.h
om.NormNoninc) (h2 : i.inv.hom.NormNoninc) : Isometry i.hom
参数：i : V ≅ W；h1 : i.hom.hom.NormNoninc；h2 : i.inv.hom.NormNoninc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SemiNormedGrp.comp_apply`：comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N)
 (g : N ⟶ O) (r : M) : (f ≫ g) r = g (f r)
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `SemiNormedGrp.id_apply`：id_apply (M : SemiNormedGrp) (r : M) : (𝟙 M : M 
⟶ M) r = r
-/
theorem iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.hom.NormNoninc)
    (h2 : i.inv.hom.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ ≤ ‖i.hom v‖ := h2 _
/-
**SemiNormedGrp.Hom.add** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{M N : SemiNormedGrp} → Add (M ⟶ N)
参数：M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.add {M N : SemiNormedGrp} : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

@[simp]
/-
**SemiNormedGrp.hom_add** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_add {V W : SemiNormedGrp} (f g : V ⟶ W) : (f + g).hom = f.hom + g.hom
参数：f g : V ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_add {V W : SemiNormedGrp} (f g : V ⟶ W) : (f + g).hom = f.hom + g.hom :=
  rfl
/-
**SemiNormedGrp.Hom.neg** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{M N : SemiNormedGrp} → Neg (M ⟶ N)
参数：M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.neg {M N : SemiNormedGrp} : Neg (M ⟶ N) where
  neg f := ofHom (- f.hom)

@[simp]
/-
**SemiNormedGrp.hom_neg** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_neg {V W : SemiNormedGrp} (f : V ⟶ W) : (-f).hom = -f.hom
参数：f : V ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_neg {V W : SemiNormedGrp} (f : V ⟶ W) : (-f).hom = -f.hom :=
  rfl
/-
**SemiNormedGrp.Hom.sub** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{M N : SemiNormedGrp} → Sub (M ⟶ N)
参数：M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.sub {M N : SemiNormedGrp} : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

@[simp]
/-
**SemiNormedGrp.hom_sub** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_sub {V W : SemiNormedGrp} (f g : V ⟶ W) : (f - g).hom = f.hom - g.hom
参数：f g : V ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_sub {V W : SemiNormedGrp} (f g : V ⟶ W) : (f - g).hom = f.hom - g.hom :=
  rfl
/-
**SemiNormedGrp.Hom.nsmul** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{M N : SemiNormedGrp} → SMul ℕ (M ⟶ N)
参数：M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.nsmul {M N : SemiNormedGrp} : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
/-
**SemiNormedGrp.hom_nsum** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_nsum {V W : SemiNormedGrp} (n : Nat) (f : V ⟶ W) : (n • f).hom = n • f
.hom
参数：n : Nat；f : V ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_nsum {V W : SemiNormedGrp} (n : ℕ) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl
/-
**SemiNormedGrp.Hom.zsmul** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{M N : SemiNormedGrp} → SMul ℤ (M ⟶ N)
参数：M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.zsmul {M N : SemiNormedGrp} : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
/-
**SemiNormedGrp.hom_zsum** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp`。
形式化陈述：hom_zsum {V W : SemiNormedGrp} (n : Int) (f : V ⟶ W) : (n • f).hom = n • f
.hom
参数：n : Int；f : V ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_zsum {V W : SemiNormedGrp} (n : ℤ) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl
/-
**SemiNormedGrp.Hom.addCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.Hom`。
形式化陈述：{V W : SemiNormedGrp} → AddCommGroup (V ⟶ W)
参数：V ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.addCommGroup {V W : SemiNormedGrp} : AddCommGroup (V ⟶ W) :=
  Function.Injective.addCommGroup _ ConcreteCategory.hom_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end SemiNormedGrp

/-- `SemiNormedGrp₁` is a type synonym for `SemiNormedGrp`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
/-
**SemiNormedGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemiNormedGrp₁` is a type synonym for `SemiNormedGrp`,
which we shall equip with the category structure consisting only of the norm non
-increasing maps.
-/
structure SemiNormedGrp₁ : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp₁` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp₁.str

namespace SemiNormedGrp₁

/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort SemiNormedGrp₁ Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp₁` -/
@[ext]
/-
**SemiNormedGrp₁.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：SemiNormedGrp₁ → SemiNormedGrp₁ → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `SemiNormedGrp₁`
-/
structure Hom (M N : SemiNormedGrp₁.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N
  normNoninc : hom'.NormNoninc
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} SemiNormedGrp₁ where
  Hom := Hom
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩
/-
**SemiNormedGrp₁.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：instFunLike (X Y : SemiNormedGrp₁) : FunLike { f : NormedAddGroupHom X Y /
/ f.NormNoninc } X Y where coe f
参数：X Y : SemiNormedGrp₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike (X Y : SemiNormedGrp₁) :
    FunLike { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  coe f := f.1.toFun
  coe_injective _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory SemiNormedGrp₁
    fun X Y => { f : NormedAddGroupHom X Y // f.NormNoninc } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : SemiNormedGrp₁) :
    AddMonoidHomClass { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  map_add f := map_add f.1
  map_zero f := map_zero f.1

/-- Turn a morphism in `SemiNormedGrp₁` back into a norm-nonincreasing `NormedAddGroupHom`. -/
/-
**SemiNormedGrp₁.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp₁.Hom`。
形式化陈述：{M N : SemiNormedGrp₁} → M.Hom N → { f // f.NormNoninc }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `SemiNormedGrp₁` back into a norm-nonincreasing `NormedAddGro
upHom`.
-/
abbrev Hom.hom {M N : SemiNormedGrp₁.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp₁) f

/-- Promote a `NormedAddGroupHom` to a morphism in `SemiNormedGrp₁`. -/
/-
**SemiNormedGrp₁.mkHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
 (f : NormedAddGroupHom M N) (i : f.NormNoninc) : SemiNormedGrp₁.of M ⟶ SemiNorm
edGrp₁.of N
参数：f : NormedAddGroupHom M N；i : f.NormNoninc。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a `NormedAddGroupHom` to a morphism in `SemiNormedGrp₁`.
-/
abbrev mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) :
    SemiNormedGrp₁.of M ⟶ SemiNormedGrp₁.of N :=
  ConcreteCategory.ofHom ⟨f, i⟩

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**SemiNormedGrp₁.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp₁.Hom.Sim
ps`。
形式化陈述：(M N : SemiNormedGrp₁) → M.Hom N → NormedAddGroupHom M.carrier N.carrier
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (M N : SemiNormedGrp₁.{u}) (f : Hom M N) : NormedAddGroupHom M N :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : SemiNormedGrp₁) : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := f.hom.1
/-
**SemiNormedGrp₁.mkHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：mkHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGr
oup N] (f : NormedAddGroupHom M N) (i : f.NormNoninc) (x) : mkHom f i x = f x
参数：f : NormedAddGroupHom M N；i : f.NormNoninc；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[ext]
/-
**SemiNormedGrp₁.ext** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：ext {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : forall (x : M), f₁ x = f₂ 
x) : f₁ = f₂
参数：h : forall (x : M), f₁ x = f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ConcreteCategory.ext_apply`：ext_apply {X Y : C} {f g : X 
⟶ Y} (h : forall x, f x = g x) : f = g

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma ext {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

@[simp]
/-
**SemiNormedGrp₁.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：hom_id {M : SemiNormedGrp₁} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {M : SemiNormedGrp₁} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/- Provided for rewriting. -/
/-
**SemiNormedGrp₁.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：id_apply (M : SemiNormedGrp₁) (r : M) : (𝟙 M : M ⟶ M) r = r
参数：M : SemiNormedGrp₁；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.id_apply`：∀ (V : Type u_1) [inst : SeminormedAddCommGr
oup V] (a : V), (NormedAddGroupHom.id V) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : SemiNormedGrp₁) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

@[simp]
/-
**SemiNormedGrp₁.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：hom_comp {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) : (f ≫ g).hom.1 
= g.hom.1.comp f.hom.1
参数：f : M ⟶ N；g : N ⟶ O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.1 = g.hom.1.comp f.hom.1 := rfl

/- Provided for rewriting. -/
/-
**SemiNormedGrp₁.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M) : (f ≫
 g) r = g (f r)
参数：f : M ⟶ N；g : N ⟶ O；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.comp_apply`：∀ {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Ty
pe u_4} [inst : SeminormedAddCommGroup V₁]   [inst_1 : SeminormedAddCommGroup V₂
] [inst_2 : Semino…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/-
**SemiNormedGrp₁.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：hom_ext {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiNormedGrp₁.Hom.ext`：∀ {M N : SemiNormedGrp₁} {x y : M.Hom N}, x.hom'
 = y.hom' → x = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma hom_ext {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext (congr_arg Subtype.val hf)

@[simp]
/-
**SemiNormedGrp₁.hom_mkHom** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：hom_mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGrou
p N] (f : NormedAddGroupHom M N) (hf : f.NormNoninc) : (mkHom f hf).hom = f
参数：f : NormedAddGroupHom M N；hf : f.NormNoninc。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : f.NormNoninc) : (mkHom f hf).hom = f := rfl

@[simp]
/-
**SemiNormedGrp₁.mkHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：mkHom_hom {M N : SemiNormedGrp₁} (f : M ⟶ N) : mkHom (Hom.hom f) f.normNon
inc = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiNormedGrp₁.Hom.normNoninc`：∀ {M N : SemiNormedGrp₁} (self : M.Hom N)
, self.hom'.NormNoninc
-/
lemma mkHom_hom {M N : SemiNormedGrp₁} (f : M ⟶ N) :
    mkHom (Hom.hom f) f.normNoninc = f := rfl

@[simp]
/-
**SemiNormedGrp₁.mkHom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：mkHom_id {M : Type u} [SeminormedAddCommGroup M] : mkHom (NormedAddGroupHo
m.id M) NormedAddGroupHom.NormNoninc.id = 𝟙 (of M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.NormNoninc.id`：id : (id V).NormNoninc
-/
lemma mkHom_id {M : Type u} [SeminormedAddCommGroup M] :
    mkHom (NormedAddGroupHom.id M) NormedAddGroupHom.NormNoninc.id = 𝟙 (of M) := rfl

@[simp]
/-
**SemiNormedGrp₁.mkHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：mkHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommG
roup N] [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGro
upHom N O) (hf : f.NormNoninc) (hg : g.NormNoninc) (hgf : (g.comp f).NormNoninc)
 : mkHom (g.comp f) hgf = mkHom f hf ≫ mkHom g hg
参数：f : NormedAddGroupHom M N；g : NormedAddGroupHom N O；hf : f.NormNoninc；hg : g.
NormNoninc；hgf : (g.comp f).NormNoninc。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O)
    (hf : f.NormNoninc) (hg : g.NormNoninc) (hgf : (g.comp f).NormNoninc) :
    mkHom (g.comp f) hgf = mkHom f hf ≫ mkHom g hg :=
  rfl

@[simp]
/-
**SemiNormedGrp₁.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：inv_hom_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M) : e.inv (e.hom r)
 = r
参数：e : M ≅ N；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SemiNormedGrp₁.comp_apply`：comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ 
N) (g : N ⟶ O) (r : M) : (f ≫ g) r = g (f r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `NormedAddGroupHom.id_apply`：∀ (V : Type u_1) [inst : SeminormedAddCommGr
oup V] (a : V), (NormedAddGroupHom.id V) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp

@[simp]
/-
**SemiNormedGrp₁.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：hom_inv_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N) : e.hom (e.inv s)
 = s
参数：e : M ≅ N；s : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SemiNormedGrp₁.comp_apply`：comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ 
N) (g : N ⟶ O) (r : M) : (f ≫ g) r = g (f r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `NormedAddGroupHom.id_apply`：∀ (V : Type u_1) [inst : SeminormedAddCommGr
oup V] (a : V), (NormedAddGroupHom.id V) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : SemiNormedGrp₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote an isomorphism in `SemiNormedGrp` to an isomorphism in `SemiNormedGrp₁`. -/
@[simps]
/-
**SemiNormedGrp₁.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f
.inv.hom.NormNoninc) : SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N where hom
参数：f : M ≅ N；i : f.hom.hom.NormNoninc；i' : f.inv.hom.NormNoninc。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote an isomorphism in `SemiNormedGrp` to an isomorphism in `SemiNormedGrp₁`.
-/
def mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f.inv.hom.NormNoninc) :
    SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N where
  hom := mkHom f.hom.hom i
  inv := mkHom f.inv.hom i'
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ SemiNormedGrp₁ SemiNormedGrp where
  forget₂ :=
    { obj := fun X => SemiNormedGrp.of X
      map := fun f => SemiNormedGrp.ofHom f.1 }
/-
**SemiNormedGrp₁.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Ty
pe u) = V
参数：V : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Type u) = V :=
  rfl
/-
**SemiNormedGrp₁.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id
参数：V : SemiNormedGrp₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id :=
  rfl
/-
**SemiNormedGrp₁.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M -> 
K) = g ∘ f
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited SemiNormedGrp₁ :=
  ⟨of PUnit⟩
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : SemiNormedGrp₁) : Zero (X ⟶ Y) where
  zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩

@[simp]
/-
**SemiNormedGrp₁.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
/-
**SemiNormedGrp₁.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁ where
/-
**SemiNormedGrp₁.isZero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp
₁`。
形式化陈述：isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZe
ro V
参数：V : SemiNormedGrp₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiNormedGrp₁.hom_ext`：hom_ext {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf
 : f.hom = g.hom) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
/-
**SemiNormedGrp₁.hasZeroObject** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiNormedGrp₁.isZero_of_subsingleton`：isZero_of_subsingleton (V : SemiN
ormedGrp₁) [Subsingleton V] : Limits.IsZero V
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
/-
**SemiNormedGrp₁.iso_isometry** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp₁`。
形式化陈述：iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom
参数：i : V ≅ W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SemiNormedGrp₁.Hom.normNoninc`：∀ {M N : SemiNormedGrp₁} (self : M.Hom N)
, self.hom'.NormNoninc
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SemiNormedGrp₁.comp_apply`：comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ 
N) (g : N ⟶ O) (r : M) : (f ≫ g) r = g (f r)
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `SemiNormedGrp₁.id_apply`：id_apply (M : SemiNormedGrp₁) (r : M) : (𝟙 M : 
M ⟶ M) r = r
-/
theorem iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V →+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _

end SemiNormedGrp₁

