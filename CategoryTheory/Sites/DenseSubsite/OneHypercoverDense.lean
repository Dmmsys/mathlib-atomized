/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Equivalence of categories of sheaves with a dense subsite that is 1-hypercover dense

Let `F : C₀ ⥤ C` be a functor equipped with Grothendieck topologies `J₀` and `J`.
Assume that `F` is a dense subsite. We introduce a typeclass
`IsOneHypercoverDense.{w} F J₀ J` which roughly says that objects in `C`
admits a `1`-hypercover consisting of objects in `C₀`.

Under the assumption that the coefficient category `A` has limits of size `w`, we
show that the restriction functor
`sheafPushforwardContinuous F A J₀ J : Sheaf J A ⥤ Sheaf J₀ A` is an equivalence
of categories (see `Functor.isEquivalence_of_isOneHypercoverDense`), which allows
to transport `HasWeakSheafify` and `HasSheafify` assumptions for the site `(C₀, J₀)`
to the site `(C, J)`, see `Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence`
and `Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` in the file
`Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean`.

-/

@[expose] public section

universe w v₀ v v' u₀ u u'

namespace CategoryTheory

open Category Limits Opposite

variable {C₀ : Type u₀} {C : Type u} [Category.{v₀} C₀] [Category.{v} C]

namespace Functor

variable (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀)
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]

/-- Given a functor `F : C₀ ⥤ C` and an object `S : C`, this structure roughly
contains the data of a pre-`1`-hypercover of `S` consisting of objects in `C₀`. -/
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：{C₀ : Type u₀} →   {C : Type u} →     [inst : CategoryTheory.Category.{v₀,
 u₀} C₀] →       [inst_1 : CategoryTheory.Category.{v, u} C] →         CategoryT
heory.Functor C₀ C → C → Type (max (max (max u₀ v) v₀) (w + 1))
参数：max (max (max u₀ v) v₀) (w + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C₀ ⥤ C` and an object `S : C`, this structure roughly
contains the data of a pre-`1`-hypercover of `S` consisting of objects in `C₀`.
-/
structure PreOneHypercoverDenseData (S : C) where
  /-- the index type of the covering of `S` -/
  I₀ : Type w
  /-- the objects in the covering of `S` -/
  X (i : I₀) : C₀
  /-- the morphisms in the covering of `S` -/
  f (i : I₀) : F.obj (X i) ⟶ S
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F} {X : C} (data : PreOneHypercoverDenseData.{w} F X)

/-- The pre-`1`-hypercover induced by a `PreOneHypercoverDenseData` structure. -/
@[simps]
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.toPreOneHypercover** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
形式化陈述：toPreOneHypercover : PreOneHypercover X where I₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreOneHypercoverDenseData.w`：∀ {C₀ : Type u₀} {C 
: Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory…

--- 原说明 ---
The pre-`1`-hypercover induced by a `PreOneHypercoverDenseData` structure.
-/
def toPreOneHypercover : PreOneHypercover X where
  I₀ := data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

/-- The sigma type of all `data.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : data.I₀ × data.I₀`. -/
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.I** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sigma type of all `data.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : data.I₀ × data.I₀`.
-/
abbrev I₁' : Type w := Sigma (fun (i : data.I₀ × data.I₀) ↦ data.I₁ i.1 i.2)

/-- The shape of the multiforks attached to `data : F.PreOneHypercoverDenseData X`. -/
@[simps]
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.multicospanShape** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
形式化陈述：multicospanShape : MulticospanShape where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of the multiforks attached to `data : F.PreOneHypercoverDenseData X`.
-/
def multicospanShape : MulticospanShape where
  L := data.I₀
  R := data.I₁'
  fst j := j.1.1
  snd j := j.1.2

/-- The diagram of the multiforks attached to `data : F.PreOneHypercoverDenseData X`. -/
@[simps]
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.multicospanIndex** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
形式化陈述：multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex data.multicospanShape A
 where left i
参数：P : C₀ᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram of the multiforks attached to `data : F.PreOneHypercoverDenseData X`
.
-/
def multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex data.multicospanShape A where
  left i := P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functoriality of the diagrams attached to `data : F.PreOneHypercoverDenseData X`
with respect to morphisms in `C₀ᵒᵖ ⥤ A`. -/
@[simps]
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.multicospanMap** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
形式化陈述：multicospanMap {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q) : (data.multicospanIndex P).mu
lticospan ⟶ (data.multicospanIndex Q).multicospan where app x
参数：f : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of the diagrams attached to `data : F.PreOneHypercoverDenseDat
a X`
with respect to morphisms in `C₀ᵒᵖ ⥤ A`.
-/
def multicospanMap {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (data.multicospanIndex P).multicospan ⟶ (data.multicospanIndex Q).multicospan where
  app x := match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁ | j₁) (i₂ | j₂) (_ | _) <;>
    simp [MulticospanIndex.multicospan]

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between the diagrams attached to `data : F.PreOneHypercoverDenseData X`
that are induced by isomorphisms in `C₀ᵒᵖ ⥤ A`. -/
@[simps]
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.multicospanMapIso** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
形式化陈述：multicospanMapIso {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q) : (data.multicospanIndex P)
.multicospan ≅ (data.multicospanIndex Q).multicospan where hom
参数：e : P ≅ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the diagrams attached to `data : F.PreOneHyperco
verDenseData X`
that are induced by isomorphisms in `C₀ᵒᵖ ⥤ A`.
-/
def multicospanMapIso {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q) :
    (data.multicospanIndex P).multicospan ≅ (data.multicospanIndex Q).multicospan where
  hom := data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

/-- Given `data : F.PreOneHypercoverDenseData X`, an object `W₀ : C₀` and two
morphisms `p₁ : W₀ ⟶ data.X i₁` and `p₂ : W₀ ⟶ data.X i₂`, this is the sieve of `W₀`
consisting of morphisms `g : Z₀ ⟶ W₀` such that there exists a morphism `Z₀ ⟶ data.Y j`
such that `g ≫ p₁ = h ≫ data.p₁ j` and `g ≫ p₂ = h ≫ data.p₂ j`. -/
@[simps]
/-
**CategoryTheory.Functor.PreOneHypercoverDenseData.sieve** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.PreOneHypercoverDenseData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `data : F.PreOneHypercoverDenseData X`, an object `W₀ : C₀` and two
morphisms `p₁ : W₀ ⟶ data.X i₁` and `p₂ : W₀ ⟶ data.X i₂`, this is the sieve of 
`W₀`
consisting of morphisms `g : Z₀ ⟶ W₀` such that there exists a morphism `Z₀ ⟶ da
ta.Y j`
such that `g ≫ p₁ = h ≫ data.p₁ j` and `g ≫ p₂ = h ≫ data.p₂ j`.
-/
def sieve₁₀ {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂) :
    Sieve W₀ where
  arrows Z₀ g := ∃ (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

end PreOneHypercoverDenseData

/-- Given a functor `F : C₀ ⥤ C`, Grothendieck topologies `J₀` on `C₀` and `J`
on `C`, an object `S. : C`, this structure roughly contains the data of a `1`-hypercover
of `S` consisting of objects in `C₀`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{C₀ : Type u₀} →   {C : Type u} →     [inst : CategoryTheory.Category.{v₀,
 u₀} C₀] →       [inst_1 : CategoryTheory.Category.{v, u} C] →         CategoryT
heory.Functor C₀ C →           CategoryTheory.GrothendieckTopology C₀ →         
    CategoryTheory.GrothendieckTopology C → C → Type (max (max (max u₀ v) v₀) (w
 + 1))
参数：max (max (max u₀ v) v₀) (w + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C₀ ⥤ C`, Grothendieck topologies `J₀` on `C₀` and `J`
on `C`, an object `S. : C`, this structure roughly contains the data of a `1`-hy
percover
of `S` consisting of objects in `C₀`.
-/
structure OneHypercoverDenseData (S : C) extends PreOneHypercoverDenseData.{w} F S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ ∈ J S
  mem₁₀ (i₁ i₂ : I₀) ⦃W₀ : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂)
    (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ ∈ J₀ W₀

/-- Given a functor `F : C₀ ⥤ C`, Grothendieck topologies `J₀` on `C₀`, this is
the property that any object in `C` has a `1`-hypercover consisting of objects in `C₀`. -/
/-
**CategoryTheory.Functor.IsOneHypercoverDense** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：{C₀ : Type u₀} →   {C : Type u} →     [inst : CategoryTheory.Category.{v₀,
 u₀} C₀] →       [inst_1 : CategoryTheory.Category.{v, u} C] →         CategoryT
heory.Functor C₀ C →           CategoryTheory.GrothendieckTopology C₀ → Category
Theory.GrothendieckTopology C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C₀ ⥤ C`, Grothendieck topologies `J₀` on `C₀`, this is
the property that any object in `C` has a `1`-hypercover consisting of objects i
n `C₀`.
-/
class IsOneHypercoverDense : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

section

variable [IsOneHypercoverDense.{w} F J₀ J]

/-- A choice of a `OneHypercoverDenseData` structure when `F` is `1`-hypercover dense. -/
/-
**CategoryTheory.Functor.oneHypercoverDenseData** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsOneHypercoverDense.nonempty_oneHypercoverDenseD
ata`：∀ {C₀ : Type u₀} {C : Type u} {inst : CategoryTheory.Category.{v₀, u₀} C₀} 
{inst_1 : CategoryTheory.Category.{v, u} C}   {F : CategoryTheory…

--- 原说明 ---
A choice of a `OneHypercoverDenseData` structure when `F` is `1`-hypercover dens
e.
-/
noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some
/-
**CategoryTheory.Functor.isDenseSubsite_of_isOneHypercoverDense** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isDenseSubsite_of_isOneHypercoverDense [F.IsLocallyFull J] [F.IsLocallyFai
thful J] (h : forall {X₀ : C₀} {S₀ : Sieve X₀}, Sieve.functorPushforward F S₀ in
 J.sieves (F.obj X₀) ↔ S₀ in J₀.sieves X₀) : IsDenseSubsite J₀ J F where isCover
Dense'
参数：h : forall {X₀ : C₀} {S₀ : Sieve X₀}, Sieve.functorPushforward F S₀ in J.siev
es (F.obj X₀) ↔ S₀ in J₀.sieves X₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₀`：∀ {C₀ : Type u₀} {C 
: Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory…
-/
lemma isDenseSubsite_of_isOneHypercoverDense [F.IsLocallyFull J] [F.IsLocallyFaithful J]
    (h : ∀ {X₀ : C₀} {S₀ : Sieve X₀},
      Sieve.functorPushforward F S₀ ∈ J.sieves (F.obj X₀) ↔ S₀ ∈ J₀.sieves X₀) :
    IsDenseSubsite J₀ J F where
  isCoverDense' := ⟨fun X ↦ by
    refine J.superset_covering ?_ (F.oneHypercoverDenseData J₀ J X).mem₀
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases h
    exact ⟨{ fac := rfl, ..}⟩⟩
  functorPushforward_mem_iff := h

end

variable [IsDenseSubsite J₀ J F]

variable {F J₀ J} in
/-- Constructor for `IsOneHypercoverDense.{w} F J₀ J` for a dense subsite
when the functor `F : C₀ ⥤ C` is fully faithful, `C` has pullbacks, and
any object in `C` admits a `w`-small covering family consisting of objects in `C₀`. -/
/-
**CategoryTheory.Functor.IsOneHypercoverDense.of_hasPullbacks** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.IsOneHypercoverDense`。
形式化陈述：∀ {C₀ : Type u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀]
 [inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor C₀ C}
 {J₀ : CategoryTheory.GrothendieckTopology C₀}   {J : CategoryTheory.Grothendiec
kTopology C} [CategoryTheory.Functor.IsDenseSubsite J₀ J F]   [CategoryTheory.Li
mits.HasPullbacks C] [F.Full] [F.Faithful],   (∀ (S : C), ∃ ι U f, CategoryTheor
y.Sieve.ofArrows (fun i => F.obj (U i)) f ∈ J S) → F.IsOneHypercoverDense J₀ J
参数：∀ (S : C), ∃ ι U f, CategoryTheory.Sieve.ofArrows (fun i => F.obj (U i)) f ∈ 
J S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.functorPushforward_mem_iff`：functorPushforward_me
m_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] : S.functorPushforward G in K
 _ ↔ S in J _
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.IsCoverDense.functorPullback_pushforward_covering
`：functorPullback_pushforward_covering [G.IsCoverDense K] [G.IsLocallyFull K] {X
 : C} (T : K (G.obj X)) : (T.val.functorPullback G).functorPus…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Constructor for `IsOneHypercoverDense.{w} F J₀ J` for a dense subsite
when the functor `F : C₀ ⥤ C` is fully faithful, `C` has pullbacks, and
any object in `C` admits a `w`-small covering family consisting of objects in `C
₀`.
-/
lemma IsOneHypercoverDense.of_hasPullbacks [HasPullbacks C] [F.Full] [F.Faithful]
    (hF : ∀ (S : C), ∃ (ι : Type w) (U : ι → C₀) (f : ∀ i, F.obj (U i) ⟶ S),
      Sieve.ofArrows _ f ∈ J S) :
    IsOneHypercoverDense.{w} F J₀ J where
  nonempty_oneHypercoverDenseData S := by
    choose ι U f hf using hF
    exact ⟨{
      I₀ := ι S
      X := U S
      f := f S
      I₁ i j := ι (pullback (f _ i) (f _ j))
      Y i j := U (pullback (f _ i) (f _ j))
      p₁ i j k := F.preimage (f _ k ≫ pullback.fst _ _)
      p₂ i j k := F.preimage (f _ k ≫ pullback.snd _ _)
      w i j k := by simp [pullback.condition]
      mem₀ := hf S
      mem₁₀ i j W₀ p₁ p₂ hp := by
        have := IsDenseSubsite.isCoverDense J₀ J F
        rw [← functorPushforward_mem_iff J₀ J F]
        refine J.superset_covering ?_
          (IsCoverDense.functorPullback_pushforward_covering
            ⟨_, J.pullback_stable (pullback.lift _ _ hp) (hf (pullback (f _ i) (f _ j)))⟩)
        rintro T _ ⟨Z, q, r, ⟨_, s, _, ⟨k⟩, fac⟩, rfl⟩
        have fac₁ := fac =≫ pullback.fst _ _
        have fac₂ := fac =≫ pullback.snd _ _
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at fac₁ fac₂
        exact ⟨Z, q, r, ⟨k, F.preimage s, F.map_injective (by simp [fac₁]),
          F.map_injective (by simp [fac₂])⟩, rfl⟩ }⟩

namespace OneHypercoverDenseData

variable {F J₀ J}

section

variable {X : C} (data : OneHypercoverDenseData.{w} F J₀ J X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.mem** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor.OneHypercoverDenseData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem₁ (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
    (w : p₁ ≫ data.f i₁ = p₂ ≫ data.f i₂) : data.toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  let S := Sieve.bind (Sieve.coverByImage F W).arrows
    (fun Y f hf ↦ ((F.imageSieve (hf.some.map ≫ p₁) ⊓
        F.imageSieve (hf.some.map ≫ p₂)).functorPushforward F).pullback hf.some.lift)
  let T := Sieve.bind S.arrows (fun Z g hg ↦ by
    letI str := Presieve.getFunctorPushforwardStructure hg.bindStruct.hg
    exact Sieve.pullback str.lift
      (Sieve.functorPushforward F (data.sieve₁₀ str.cover.1.choose str.cover.2.choose)))
  have hS : S ∈ J W := by
    apply J.bind_covering
    · apply is_cover_of_isCoverDense
    · intro Y f hf
      apply J.pullback_stable
      rw [Functor.functorPushforward_mem_iff J₀]
      apply J₀.intersection_covering
      all_goals apply IsDenseSubsite.imageSieve_mem J₀ J
  have hT : T ∈ J W := J.bind_covering hS (fun Z g hg ↦ by
    apply J.pullback_stable
    rw [Functor.functorPushforward_mem_iff J₀]
    let str := Presieve.getFunctorPushforwardStructure hg.bindStruct.hg
    apply data.mem₁₀
    simp only [str.cover.1.choose_spec, str.cover.2.choose_spec, assoc, w])
  refine J.superset_covering ?_ hT
  rintro U f ⟨V, a, b, hb, h, _, rfl⟩
  let str := Presieve.getFunctorPushforwardStructure hb.bindStruct.hg
  obtain ⟨W₀, c : _ ⟶ _, d, ⟨j, e, h₁, h₂⟩, fac⟩ := h
  dsimp
  refine ⟨j, d ≫ F.map e, ?_, ?_⟩
  · rw [assoc, assoc, ← F.map_comp, ← h₁, F.map_comp, ← reassoc_of% fac,
      str.cover.1.choose_spec, ← reassoc_of% str.fac,
      Presieve.CoverByImageStructure.fac_assoc,
      Presieve.BindStruct.fac_assoc]
  · rw [assoc, assoc, ← F.map_comp, ← h₂, F.map_comp, ← reassoc_of% fac,
      str.cover.2.choose_spec, ← reassoc_of% str.fac,
      Presieve.CoverByImageStructure.fac_assoc,
      Presieve.BindStruct.fac_assoc]

/-- The `1`-hypercover associated to a `OneHypercoverDenseData` structure. -/
@[simps toPreOneHypercover]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.toOneHypercover** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：toOneHypercover {X : C} (data : F.OneHypercoverDenseData J₀ J X) : J.OneHy
percover X where toPreOneHypercover
参数：data : F.OneHypercoverDenseData J₀ J X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₀`：∀ {C₀ : Type u₀} {C 
: Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₁`：mem₁ (i₁ i₂ : data.I
₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂)) (w : p₁ ≫ d
ata.f i₁ = p₂ ≫ data.f i₂) : data.toPreO…

--- 原说明 ---
The `1`-hypercover associated to a `OneHypercoverDenseData` structure.
-/
def toOneHypercover {X : C} (data : F.OneHypercoverDenseData J₀ J X) :
    J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

variable {X : C} (data : OneHypercoverDenseData.{w} F J₀ J X) {X₀ : C₀} (f : F.obj X₀ ⟶ X)

/-- Auxiliary structure for the definition `OneHypercoverDenseData.sieve`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.SieveStruct** 是 Mathlib 中的一个结构，位
于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：SieveStruct {Y₀ : C₀} (g : Y₀ ⟶ X₀) where /-- the index of the intermediat
e object -/ i₀ : data.I₀ /-- the morphism that is part of the factorization `fac
`. -/ q : F.obj Y₀ ⟶ F.obj (data.X i₀) fac : q ≫ data.f i₀ = F.map g ≫ f
参数：g : Y₀ ⟶ X₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary structure for the definition `OneHypercoverDenseData.sieve`.
-/
structure SieveStruct {Y₀ : C₀} (g : Y₀ ⟶ X₀) where
  /-- the index of the intermediate object -/
  i₀ : data.I₀
  /-- the morphism that is part of the factorization `fac`. -/
  q : F.obj Y₀ ⟶ F.obj (data.X i₀)
  fac : q ≫ data.f i₀ = F.map g ≫ f := by simp

attribute [reassoc (attr := simp)] SieveStruct.fac

/-- Given `data : OneHypercoverDenseData F J₀ J X` and a morphism `f : F.obj X₀ ⟶ X`,
this is the sieve of `X₀` consisting of morphisms `g : Y₀ ⟶ X₀` such that there
exists `i₀ : data.I₀`, `q : F.obj Y₀ ⟶ F.obj (data.X i₀)` such that
we have a factorization `q ≫ data.f i₀ = F.map g ≫ f`. -/
@[simps]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.sieve** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：sieve : Sieve X₀ where arrows Y₀ g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `data : OneHypercoverDenseData F J₀ J X` and a morphism `f : F.obj X₀ ⟶ X`
,
this is the sieve of `X₀` consisting of morphisms `g : Y₀ ⟶ X₀` such that there
exists `i₀ : data.I₀`, `q : F.obj Y₀ ⟶ F.obj (data.X i₀)` such that
we have a factorization `q ≫ data.f i₀ = F.map g ≫ f`.
-/
def sieve : Sieve X₀ where
  arrows Y₀ g := Nonempty (SieveStruct data f g)
  downward_closed := by
    rintro Y₀ Z₀ g ⟨h⟩ p
    exact ⟨{ i₀ := h.i₀, q := F.map p ≫ h.q, fac := by rw [assoc, h.fac, map_comp_assoc]}⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.sieve_mem** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：sieve_mem : sieve data f in J₀ X₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.functorPushforward_mem_iff`：functorPushforward_me
m_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] : S.functorPushforward G in K
 _ ↔ S in J _
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.ofArrows.fac`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i ⟶ X
}   {W : C} {g : W ⟶ X}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Presieve.CoverByImageStructure.fac_assoc`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] {G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.bind_covering`：bind_covering {S : Si
eve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X) (hR : fo
rall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in …
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₀`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S), s…
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用引理 `CategoryTheory.Functor.functorPushforward_imageSieve_mem`：functorPushfor
ward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) : (G.image
Sieve f).functorPushforward G in K _
-/
lemma sieve_mem : sieve data f ∈ J₀ X₀ := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  have := IsDenseSubsite.isLocallyFull J₀ J F
  rw [← functorPushforward_mem_iff J₀ J F]
  let R : ⦃W : C⦄ → ⦃p : W ⟶ F.obj X₀⦄ →
    (Sieve.pullback f data.toOneHypercover.sieve₀).arrows p → Sieve W := fun W p hp ↦
      Sieve.bind (Sieve.coverByImage F W).arrows (fun U π hπ ↦
        Sieve.pullback hπ.some.lift
          (Sieve.functorPushforward F (F.imageSieve (hπ.some.map ≫ p))))
  refine J.superset_covering ?_
    (J.bind_covering (J.pullback_stable f (data.toOneHypercover.mem₀)) (R := R)
    (fun W p hp ↦ J.bind_covering (F.is_cover_of_isCoverDense J W) ?_))
  · rintro W' _ ⟨W, _, p, hp, ⟨Y₀, a, b, hb, ⟨U, c, d, ⟨x₁, w₁⟩, fac⟩, rfl⟩, rfl⟩
    have hp' := Sieve.ofArrows.fac hp
    dsimp at hp'
    refine ⟨U, x₁, d, ⟨Sieve.ofArrows.i hp,
      F.map c ≫ (Nonempty.some hb).map ≫ Sieve.ofArrows.h hp, ?_⟩, ?_⟩
    · rw [w₁, assoc, assoc, assoc, assoc, hp']
    · rw [w₁, assoc, ← reassoc_of% fac, hb.some.fac_assoc]
  · intro U π hπ
    apply J.pullback_stable
    apply functorPushforward_imageSieve_mem

end

section

namespace isSheaf_iff

variable {data : ∀ X, F.OneHypercoverDenseData J₀ J X} {G : Cᵒᵖ ⥤ A}
  (hG₀ : Presheaf.IsSheaf J₀ (F.op ⋙ G))
  (hG : ∀ (X : C), IsLimit ((data X).toOneHypercover.multifork G))
  {X : C} (S : J.Cover X)

section

variable {S} (s : Multifork (S.index G))

/-- Auxiliary definition for `lift`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.liftAux** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `lift`.
-/
private noncomputable def liftAux (i : (data X).I₀) : s.pt ⟶ G.obj (op (F.obj ((data X).X i))) :=
  hG₀.amalgamate ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩
    (fun ⟨W₀, a, ha⟩ ↦ s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩) (by
      rintro ⟨W₀, a, ha⟩ ⟨Z₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
      exact s.condition
        { fst := ⟨_, _, ha⟩
          snd := ⟨_, _, hb⟩
          r := ⟨_, F.map p₁, F.map p₂, by
              simp only [← Functor.map_comp_assoc, fac]⟩ })
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.liftAux_fac** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma liftAux_fac {i : (data X).I₀} {W₀ : C₀} (a : W₀ ⟶ (data X).X i)
    (ha : S (F.map a ≫ (data X).f i)) :
    liftAux hG₀ s i ≫ G.map (F.map a).op = s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩ :=
  hG₀.amalgamate_map _ _ _ ⟨W₀, a, ha⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the lemma `OneHypercoverDenseData.isSheaf_iff`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.lift** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the lemma `OneHypercoverDenseData.isSheaf_iff`.
-/
private noncomputable def lift : s.pt ⟶ G.obj (op X) :=
  Multifork.IsLimit.lift (hG X) (fun i ↦ liftAux hG₀ s i) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    dsimp at i₁ i₂ j ⊢
    refine Presheaf.IsSheaf.hom_ext
      hG₀ ⟨_, cover_lift F J₀ _
        (J.pullback_stable (F.map ((data X).p₁ j) ≫ (data X).f i₁) S.2)⟩ _ _ ?_
    rintro ⟨W₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp]
    have ha₁ : S (F.map (a ≫ (data X).p₁ j) ≫ (data X).f i₁) := by simpa using ha
    have ha₂ : S (F.map (a ≫ (data X).p₂ j) ≫ (data X).f i₂) := by
      rwa [Functor.map_comp_assoc, ← (data X).w j]
    rw [liftAux_fac _ _ _ ha₁, liftAux_fac _ _ _ ha₂]
    congr 2
    rw [map_comp_assoc, map_comp_assoc, (data X).w j])

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.lift_map** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lift_map (i : (data X).I₀) :
    lift hG₀ hG s ≫ G.map ((data X).f i).op = liftAux hG₀ s i :=
  Multifork.IsLimit.fac _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.fac** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma fac (a : S.Arrow) :
    lift hG₀ hG s ≫ G.map a.f.op = s.ι a :=
  Multifork.IsLimit.hom_ext (hG _) (fun i ↦
    Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _
        (J.pullback_stable ((data a.Y).f i ≫ a.f) (data X).mem₀)⟩ _ _ (by
        rintro ⟨X₀, b, ⟨_, c, _, h, fac₁⟩⟩
        obtain ⟨j⟩ := h
        refine Presheaf.IsSheaf.hom_ext hG₀
          ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F c⟩ _ _ ?_
        rintro ⟨Y₀, d, e, fac₂⟩
        dsimp at i j c fac₁ ⊢
        have he : S (F.map e ≫ (data X).f j) := by
          rw [fac₂, assoc, fac₁]
          simpa only [assoc] using S.1.downward_closed a.hf (F.map d ≫ F.map b ≫ (data a.Y).f i)
        simp only [assoc, ← Functor.map_comp, ← op_comp, ← fac₁]
        conv_lhs => simp only [op_comp, Functor.map_comp, assoc, lift_map_assoc]
        rw [← Functor.map_comp, ← op_comp, ← fac₂, liftAux_fac _ _ _ he]
        simpa using s.condition
          { fst := { hf := he, .. }
            snd := a
            r := ⟨_, 𝟙 _, F.map d ≫ F.map b ≫ (data a.Y).f i, by
              simp only [fac₁, fac₂, assoc, id_comp]⟩ }))

set_option backward.isDefEq.respectTransparency false in
variable {s} in
include hG hG₀ in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.hom_ext** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hom_ext {f₁ f₂ : s.pt ⟶ G.obj (op X)}
    (h : ∀ (a : S.Arrow), f₁ ≫ G.map a.f.op = f₂ ≫ G.map a.f.op) : f₁ = f₂ :=
  Multifork.IsLimit.hom_ext (hG X) (fun i ↦ by
    refine Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩ _ _ ?_
    rintro ⟨X₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp]
    exact h ⟨_, _, ha⟩)

end

/-- Auxiliary definition for the lemma `OneHypercoverDenseData.isSheaf_iff`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff.isLimit** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the lemma `OneHypercoverDenseData.isSheaf_iff`.
-/
private noncomputable def isLimit : IsLimit (S.multifork G) :=
  Multifork.IsLimit.mk _
    (lift hG₀ hG) (fac hG₀ hG) (fun s _ hm ↦
      hom_ext hG₀ hG (fun a ↦ (hm a).trans (fac hG₀ hG s a).symm))

end isSheaf_iff

/-- Let `F : C₀ ⥤ C` be a dense subsite, and assume we have a family
`data : ∀ X, F.OneHypercoverDenseData J₀ J X`.
This lemma shows that `G : Cᵒᵖ ⥤ A` is a sheaf iff `F.op F.op ⋙ G : C₀ᵒᵖ ⥤ A`
is a sheaf and for any `X : C`, the multifork for `G` and the `1`-hypercover
given by `data X` is a limit. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：isSheaf_iff (data : forall X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ 
A) : Presheaf.IsSheaf J G ↔ Presheaf.IsSheaf J₀ (F.op ⋙ G) ∧ forall (X : C), Non
empty (IsLimit ((data X).toOneHypercover.multifork G))
参数：data : forall X, F.OneHypercoverDenseData J₀ J X；G : Cᵒᵖ ⥤ A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf`：op_comp_isSheaf [Functor.IsConti
nuous F J K] (G : Sheaf K A) : Presheaf.IsSheaf J (F.op ⋙ G.obj)
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_multifork`：isSheaf_iff_multifork : I
sSheaf J P ↔ forall (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P))

--- 原说明 ---
Let `F : C₀ ⥤ C` be a dense subsite, and assume we have a family
`data : ∀ X, F.OneHypercoverDenseData J₀ J X`.
This lemma shows that `G : Cᵒᵖ ⥤ A` is a sheaf iff `F.op F.op ⋙ G : C₀ᵒᵖ ⥤ A`
is a sheaf and for any `X : C`, the multifork for `G` and the `1`-hypercover
given by `data X` is a limit.
-/
lemma isSheaf_iff (data : ∀ X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J G ↔
      Presheaf.IsSheaf J₀ (F.op ⋙ G) ∧
        ∀ (X : C), Nonempty (IsLimit ((data X).toOneHypercover.multifork G)) := by
  refine ⟨fun hG ↦ ⟨op_comp_isSheaf F J₀ J ⟨_, hG⟩,
    fun X ↦ ⟨(data X).toOneHypercover.isLimitMultifork ⟨G, hG⟩⟩⟩, fun ⟨hG₀, hG⟩ ↦ ?_⟩
  rw [Presheaf.isSheaf_iff_multifork]
  replace hG := fun X ↦ (hG X).some
  exact fun X S ↦ ⟨isSheaf_iff.isLimit hG₀ hG S⟩

end

section

variable (data : ∀ X, OneHypercoverDenseData.{w} F J₀ J X)
  [HasLimitsOfSize.{w, w} A]

namespace essSurj

variable (G₀ : Sheaf J₀ A)

/-- Given a dense subsite `F : C₀ ⥤ C` and a family
`data : ∀ X, OneHypercoverDenseData F J₀ J X` and a sheaf `G₀` on `J₀`,
this is the value on an object `X : C` of the "extension" of `G₀`
as a sheaf on `J` (see `OneHypercoverDenseData.essSurj.presheaf` and
`OneHypercoverDenseData.essSurj.isSheaf`): it is defined as
a multiequalizer using `data X`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafObj (X : C) : A
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a dense subsite `F : C₀ ⥤ C` and a family
`data : ∀ X, OneHypercoverDenseData F J₀ J X` and a sheaf `G₀` on `J₀`,
this is the value on an object `X : C` of the "extension" of `G₀`
as a sheaf on `J` (see `OneHypercoverDenseData.essSurj.presheaf` and
`OneHypercoverDenseData.essSurj.isSheaf`): it is defined as
a multiequalizer using `data X`.
-/
noncomputable def presheafObj (X : C) : A :=
  multiequalizer ((data X).multicospanIndex G₀.obj)

/-- The projection `presheafObj data G₀ X ⟶ G₀.val.obj (op ((data X).X i))`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafObj (X : C) : A
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `presheafObj data G₀ X ⟶ G₀.val.obj (op ((data X).X i))`.
-/
noncomputable def presheafObjπ (X : C) (i : (data X).I₀) :
    presheafObj data G₀ X ⟶ G₀.obj.obj (op ((data X).X i)) :=
  Multiequalizer.ι ((data X).multicospanIndex G₀.obj) i

omit [IsDenseSubsite J₀ J F] in
variable {data G₀} in
@[ext]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_hom_ext** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X} (h :
 forall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ presheafObjπ data 
G₀ X i) : f = g
参数：h : forall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ presheafObjπ
 data G₀ X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
-/
lemma presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X}
    (h : ∀ (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ presheafObjπ data G₀ X i) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ h

omit [IsDenseSubsite J₀ J F] in
@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_condition** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafObj_condition (X : C) (i i' : (data X).I₀) (j : (data X).I₁ i i') 
: presheafObjπ data G₀ X i ≫ G₀.obj.map ((data X).p₁ j).op = presheafObjπ data G
₀ X i' ≫ G₀.obj.map ((data X).p₂ j).op
参数：X : C；i i' : (data X).I₀；j : (data X).I₁ i i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multiequalizer.condition`：condition (b) : Multiequ
alizer.ι I (J.fst b) ≫ I.fst b = Multiequalizer.ι I (J.snd b) ≫ I.snd b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma presheafObj_condition (X : C) (i i' : (data X).I₀) (j : (data X).I₁ i i') :
    presheafObjπ data G₀ X i ≫ G₀.obj.map ((data X).p₁ j).op =
    presheafObjπ data G₀ X i' ≫ G₀.obj.map ((data X).p₂ j).op :=
  Multiequalizer.condition ((data X).multicospanIndex G₀.obj) ⟨⟨i, i'⟩, j⟩
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_mapPreimage_
condition** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseDa
ta.essSurj`。
形式化陈述：presheafObj_mapPreimage_condition (X : C) (i₁ i₂ : (data X).I₀) {Y₀ : C₀} 
(p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((data X).X i₂)) 
(fac : p₁ ≫ (data X).f i₁ = p₂ ≫ (data X).f i₂) : presheafObjπ data G₀ X i₁ ≫ Is
DenseSubsite.mapPreimage J F G₀ p₁ = presheafObjπ data G₀ X i₂ ≫ IsDenseSubsite.
mapPreimage J F G₀ p₂
参数：X : C；i₁ i₂ : (data X).I₀；p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)；p₂ : F.obj Y₀
 ⟶ F.obj ((data X).X i₂)；fac : p₁ ≫ (data X).f i₁ = p₂ ≫ (data X).f i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₁₀`：∀ {C₀ : Type u₀} {C
 : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory
.Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map_of_fac`：mapPreimag
e_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (p : Z ⟶ X) (g : Z ⟶ Y) (fac : 
G.map p ≫ f = G.map g) : mapPreimage K G F f ≫ F.o…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_condit
ion_assoc`：∀ {C₀ : Type u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀
} C₀] [inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory…
-/
lemma presheafObj_mapPreimage_condition
    (X : C) (i₁ i₂ : (data X).I₀) {Y₀ : C₀}
    (p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((data X).X i₂))
    (fac : p₁ ≫ (data X).f i₁ = p₂ ≫ (data X).f i₂) :
    presheafObjπ data G₀ X i₁ ≫ IsDenseSubsite.mapPreimage J F G₀ p₁ =
      presheafObjπ data G₀ X i₂ ≫ IsDenseSubsite.mapPreimage J F G₀ p₂ := by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_,
    J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F p₁)
      (IsDenseSubsite.imageSieve_mem J₀ J F p₂)⟩ _ _ ?_
  intro ⟨W₀, a, ⟨b₁, h₁⟩, ⟨b₂, h₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ i₁ i₂ b₁ b₂ (by simp only [h₁, h₂, assoc, fac])⟩ _ _ ?_
  intro ⟨U₀, c, ⟨j, t, fac₁, fac₂⟩⟩
  simp only [assoc, ← Functor.map_comp, ← op_comp,
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ p₁ (c ≫ a) (c ≫ b₁) (by simp [← h₁]),
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ p₂ (c ≫ a) (c ≫ b₂) (by simp [← h₂])]
  simpa [fac₁, fac₂] using presheafObj_condition_assoc _ _ _ _ _ _ _

/-- The (limit) multifork with point `presheafObjπ data G₀ X` for
the diagram given by `G₀` and `data X`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjMultifork** 是
 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`
。
形式化陈述：presheafObjMultifork (X : C) : Multifork ((data X).multicospanIndex G₀.obj
)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (limit) multifork with point `presheafObjπ data G₀ X` for
the diagram given by `G₀` and `data X`.
-/
noncomputable abbrev presheafObjMultifork (X : C) :
    Multifork ((data X).multicospanIndex G₀.obj) :=
  Multifork.ofι _ (presheafObj data G₀ X) (presheafObjπ data G₀ X)
    (fun _ ↦ presheafObj_condition _ _ _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The multifork `presheafObjMultifork` is a limit. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjIsLimit** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafObjIsLimit (X : C) : IsLimit (presheafObjMultifork data G₀ X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multifork `presheafObjMultifork` is a limit.
-/
noncomputable def presheafObjIsLimit (X : C) :
    IsLimit (presheafObjMultifork data G₀ X) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Multifork.ext (Iso.refl _))

namespace restriction

/-- Auxiliary definition for `OneHypercoverDenseData.essSurj.restriction`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction.res** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restric
tion`。
形式化陈述：res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀} (h : SieveStruct
 (data X) f g) : presheafObj data G₀ X ⟶ G₀.obj.obj (op Y₀)
参数：h : SieveStruct (data X) f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `OneHypercoverDenseData.essSurj.restriction`.
-/
noncomputable def res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h : SieveStruct (data X) f g) :
    presheafObj data G₀ X ⟶ G₀.obj.obj (op Y₀) :=
  presheafObjπ data G₀ X h.i₀ ≫ IsDenseSubsite.mapPreimage J F G₀ h.q
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction.res_eq_res**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.
restriction`。
形式化陈述：res_eq_res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀} (h₁ h₂ : 
SieveStruct (data X) f g) : res data G₀ h₁ = res data G₀ h₂
参数：h₁ h₂ : SieveStruct (data X) f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₁₀`：∀ {C₀ : Type u₀} {C
 : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory
.Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.SieveStruct.fac`：∀ {C₀ : T
ype u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp_map`：mapPreimage_
comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : Z ⟶ X) : mapPreimage K G F f ≫
 F.obj.map g.op = mapPreimage K G F (G.map g ≫ f…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_mapPre
image_condition`：presheafObj_mapPreimage_condition (X : C) (i₁ i₂ : (data X).I₀)
 {Y₀ : C₀} (p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((d…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma res_eq_res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h₁ h₂ : SieveStruct (data X) f g) :
    res data G₀ h₁ = res data G₀ h₂ := by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F h₁.q)
      (IsDenseSubsite.imageSieve_mem J₀ J F h₂.q)⟩ _ _ ?_
  rintro ⟨Z₀, a, ⟨b₁, w₁⟩, ⟨b₂, w₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ b₁ b₂ (by rw [w₁, w₂, assoc, assoc, h₁.fac, h₂.fac])⟩ _ _ ?_
  rintro ⟨W₀, c, hc⟩
  dsimp [res]
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map]
  apply presheafObj_mapPreimage_condition
  simp

end restriction

/-- Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀ J X`
be a family. Let `G₀` be a sheaf on `C₀`. Let `f : F.obj X₀ ⟶ X`.
This is the canonical morphism
`presheafObj data G₀ X ⟶ G₀.obj.obj (op X₀)` (where `presheafObj data G₀ X`
is the value on `X` of the extension to `C` of the sheaf `G₀`,
see `OneHypercoverDenseData.essSurj.presheaf` and
`OneHypercoverDenseData.essSurj.isSheaf`). -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：restriction {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) : presheafObj data G₀ X ⟶
 G₀.obj.obj (op X₀)
参数：f : F.obj X₀ ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀
 J X`
be a family. Let `G₀` be a sheaf on `C₀`. Let `f : F.obj X₀ ⟶ X`.
This is the canonical morphism
`presheafObj data G₀ X ⟶ G₀.obj.obj (op X₀)` (where `presheafObj data G₀ X`
is the value on `X` of the extension to `C` of the sheaf `G₀`,
see `OneHypercoverDenseData.essSurj.presheaf` and
`OneHypercoverDenseData.essSurj.isSheaf`).
-/
noncomputable def restriction {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) :
    presheafObj data G₀ X ⟶ G₀.obj.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩
    (fun ⟨Y₀, g, hg⟩ ↦ restriction.res data G₀ hg.some) (by
      rintro ⟨Z₁, g₁, ⟨h₁⟩⟩ ⟨Z₂, g₂, ⟨h₂⟩⟩ ⟨T₀, p₁, p₂, w⟩
      dsimp at g₁ g₂ p₁ p₂ w ⊢
      rw [restriction.res_eq_res data G₀ _ h₁, restriction.res_eq_res data G₀ _ h₂]
      refine Presheaf.IsSheaf.hom_ext G₀.property
        ⟨_, J₀.intersection_covering
          (IsDenseSubsite.imageSieve_mem J₀ J F (F.map p₁ ≫ h₁.q))
          (IsDenseSubsite.imageSieve_mem J₀ J F (F.map p₂ ≫ h₂.q))⟩ _ _ ?_
      rintro ⟨W₀, a, ⟨q₁, w₁⟩, ⟨q₂, w₂⟩⟩
      refine Presheaf.IsSheaf.hom_ext G₀.property
        ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ q₁ q₂ (by
        simp only [w₁, w₂, assoc, h₁.fac, h₂.fac, ← Functor.map_comp_assoc, w])⟩ _ _ ?_
      rintro ⟨U₀, b, hb⟩
      dsimp
      simp only [assoc, restriction.res, IsDenseSubsite.mapPreimage_comp_map]
      apply presheafObj_mapPreimage_condition
      simp only [assoc, h₁.fac, h₂.fac, ← Functor.map_comp_assoc, w])

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_map** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：restriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀} (g : Y₀ ⟶ X
₀) {i : (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i)) (fac : p ≫ (data X).f
 i = F.map g ≫ f) : restriction data G₀ f ≫ G₀.obj.map g.op = presheafObjπ data 
G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p
参数：f : F.obj X₀ ⟶ X；g : Y₀ ⟶ X₀；data X；p : F.obj Y₀ ⟶ F.obj ((data X).X i)；fac :
 p ≫ (data X).f i = F.map g ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.amalgamate_map`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} 
{A : Type u₂}   [inst_1 : CategoryTh…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_mapPre
image_condition`：presheafObj_mapPreimage_condition (X : C) (i₁ i₂ : (data X).I₀)
 {Y₀ : C₀} (p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((d…
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.SieveStruct.fac`：∀ {C₀ : T
ype u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory…
-/
lemma restriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀}
    (g : Y₀ ⟶ X₀) {i : (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i))
    (fac : p ≫ (data X).f i = F.map g ≫ f) :
    restriction data G₀ f ≫ G₀.obj.map g.op =
      presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  have hg : (data X).sieve f g := ⟨i, p, fac⟩
  dsimp only [restriction]
  rw [G₀.2.amalgamate_map _ _ _ ⟨_, g, hg⟩]
  apply presheafObj_mapPreimage_condition
  rw [hg.some.fac, fac]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_eq_of_fac** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：restriction_eq_of_fac {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {i : (data X).I
₀} (p : F.obj X₀ ⟶ F.obj ((data X).X i)) (fac : p ≫ (data X).f i = f) : restrict
ion data G₀ f = presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p
参数：f : F.obj X₀ ⟶ X；data X；p : F.obj X₀ ⟶ F.obj ((data X).X i)；fac : p ≫ (data X
).f i = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_map`：r
estriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀} (g : Y₀ ⟶ X₀) {i :
 (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i)) (fac : …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma restriction_eq_of_fac {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
    {i : (data X).I₀} (p : F.obj X₀ ⟶ F.obj ((data X).X i))
    (fac : p ≫ (data X).f i = f) :
    restriction data G₀ f =
      presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  simpa using restriction_map data G₀ f (𝟙 _) p (by simpa using fac)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `OneHypercoverDenseData.essSurj.presheaf`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafMap {X Y : C} (f : X ⟶ Y) : presheafObj data G₀ Y ⟶ presheafObj da
ta G₀ X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `OneHypercoverDenseData.essSurj.presheaf`.
-/
noncomputable def presheafMap {X Y : C} (f : X ⟶ Y) :
    presheafObj data G₀ Y ⟶ presheafObj data G₀ X :=
  Multiequalizer.lift _ _ (fun i₀ ↦ restriction data G₀ ((data X).f i₀ ≫ f)) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    obtain ⟨a, h₁, h₂⟩ : ∃ a, a = F.map ((data X).p₁ j) ≫ (data X).f i₁ ≫ f ∧
        a = F.map ((data X).p₂ j) ≫ (data X).f i₂ ≫ f := ⟨_, rfl, (data X).w_assoc j _⟩
    refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, cover_lift F J₀ _ (J.pullback_stable a (data Y).mem₀)⟩ _ _ ?_
    rintro ⟨W₀, b, ⟨_, p, _, ⟨i⟩, fac⟩⟩
    dsimp at fac ⊢
    simp only [assoc, ← map_comp, ← op_comp]
    rw [restriction_map (p := p), restriction_map (p := p)]
    all_goals simp_all)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma presheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) :
    presheafMap data G₀ f ≫ presheafObjπ data G₀ X i =
      restriction data G₀ ((data X).f i ≫ f) :=
  Multiequalizer.lift_ι _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_restriction*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj
`。
形式化陈述：presheafMap_restriction {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y)
 : presheafMap data G₀ g ≫ restriction data G₀ f = restriction data G₀ (f ≫ g)
参数：f : F.obj X₀ ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.GrothendieckTopology.bind_covering`：bind_covering {S : Si
eve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X) (hR : fo
rall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in …
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsCocontinuous`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₀`：∀ {C₀ : Type u₀} {C 
: Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `CategoryTheory.Sieve.ofArrows.fac`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i ⟶ X
}   {W : C} {g : W ⟶ X}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_map`：r
estriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀} (g : Y₀ ⟶ X₀) {i :
 (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i)) (fac : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_π_asso
c`：∀ {C₀ : Type u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [i
nst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map_of_fac`：mapPreimag
e_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (p : Z ⟶ X) (g : Z ⟶ Y) (fac : 
G.map p ≫ f = G.map g) : mapPreimage K G F f ≫ F.o…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map`：mapPreimage_map {
X Y : C} (f : X ⟶ Y) : mapPreimage K G F (G.map f) = F.obj.map f.op
-/
lemma presheafMap_restriction {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y) :
    presheafMap data G₀ g ≫ restriction data G₀ f = restriction data G₀ (f ≫ g) := by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_, GrothendieckTopology.bind_covering
    (hS := cover_lift F J₀ J (J.pullback_stable f (data X).mem₀)) (hR := fun Y₀ a ha ↦
      cover_lift F J₀ J (J.pullback_stable
        (Sieve.ofArrows.h ha ≫ (data X).f (Sieve.ofArrows.i ha) ≫ g) (data Y).mem₀))⟩ _ _ ?_
  rintro ⟨U₀, _, Y₀, c, d, hd, hc, rfl⟩
  have hc' := Sieve.ofArrows.fac hc
  have hd' := Sieve.ofArrows.fac hd
  dsimp at hc hd hc' hd' ⊢
  /- #adaptation_note Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed the `fac`
  arguments below (i.e. `fac := by grind`). It is not yet clear whether this is due to defeq
  abuse in Mathlib or a problem in the new canonicalizer; a minimization would help. -/
  rw [assoc, ← op_comp, restriction_map (i := Sieve.ofArrows.i hd)
    (p := F.map c ≫ Sieve.ofArrows.h hd) (fac := by simp; grind),
    restriction_map (i := Sieve.ofArrows.i hc) (p := Sieve.ofArrows.h hc) (fac := by simp; grind),
    presheafMap_π_assoc]
  dsimp
  have := J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F (Sieve.ofArrows.h hc))
    (J₀.pullback_stable c (IsDenseSubsite.imageSieve_mem J₀ J F (Sieve.ofArrows.h hd)))
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_, this⟩ _ _ ?_
  rintro ⟨V₀, a, ⟨x₁, fac₁⟩, ⟨x₂, fac₂⟩⟩
  dsimp
  rw [assoc, assoc,
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ _ _ x₂ (by simpa using fac₂.symm),
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ _ _ x₁ fac₁.symm]
  /- #adaptation_note Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), the last argument below was
  `by grind` (now `by simp_all`). It is not yet clear whether this is due to defeq abuse in
  Mathlib or a problem in the new canonicalizer; a minimization would help. -/
  rw [restriction_map data G₀ _ _ (F.map x₁) (by simp_all), IsDenseSubsite.mapPreimage_map]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_id** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafMap_id (X : C) : presheafMap data G₀ (𝟙 X) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_hom_ex
t`：presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X} (h : fo
rall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ pres…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_π`：pre
sheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) : presheafMap data G₀ f ≫ pre
sheafObjπ data G₀ X i = restriction data G₀ ((data X).f i…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_eq_of_
fac`：restriction_eq_of_fac {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {i : (data X).I₀
} (p : F.obj X₀ ⟶ F.obj ((data X).X i)) (fac : p ≫ (data X).f i =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_id`：mapPreimage_id (X 
: C) : mapPreimage K G F (𝟙 (G.obj X)) = 𝟙 _
-/
lemma presheafMap_id (X : C) :
    presheafMap data G₀ (𝟙 X) = 𝟙 _ := by
  ext i
  rw [presheafMap_π, comp_id, id_comp,
    restriction_eq_of_fac data G₀ ((data X).f i) (𝟙 _) (by simp),
    IsDenseSubsite.mapPreimage_id, comp_id]

@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_comp** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : presheafMap data G₀
 (f ≫ g) = presheafMap data G₀ g ≫ presheafMap data G₀ f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_hom_ex
t`：presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X} (h : fo
rall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ pres…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_π`：pre
sheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) : presheafMap data G₀ f ≫ pre
sheafObjπ data G₀ X i = restriction data G₀ ((data X).f i…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_restri
ction`：presheafMap_restriction {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y
) : presheafMap data G₀ g ≫ restriction data G₀ f = restriction dat…
-/
lemma presheafMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    presheafMap data G₀ (f ≫ g) = presheafMap data G₀ g ≫ presheafMap data G₀ f := by
  ext i
  rw [assoc, presheafMap_π, presheafMap_π, presheafMap_restriction, assoc]

/-- Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀ J X`
be a family. Let `G₀` be a sheaf on `C₀`. This is a presheaf on `C` which
extends `G₀` (see `OneHypercoverDenseData.essSurj.compPresheafIso`) and it is a sheaf
(see `OneHypercoverDenseData.essSurj.isSheaf`). -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheaf** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheaf : Cᵒᵖ ⥤ A where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀
 J X`
be a family. Let `G₀` be a sheaf on `C₀`. This is a presheaf on `C` which
extends `G₀` (see `OneHypercoverDenseData.essSurj.compPresheafIso`) and it is a 
sheaf
(see `OneHypercoverDenseData.essSurj.isSheaf`).
-/
noncomputable def presheaf : Cᵒᵖ ⥤ A where
  obj X := presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id X := presheafMap_id data G₀ X.unop
  map_comp f g := presheafMap_comp data G₀ g.unop f.unop

namespace presheafObjObjIso

variable (X₀ : C₀)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `OneHypercoverDenseData.essSurj.presheafObjObjIso`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.hom** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.p
resheafObjObjIso`。
形式化陈述：hom : (presheaf data G₀).obj (op (F.obj X₀)) ⟶ G₀.obj.obj (op X₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `OneHypercoverDenseData.essSurj.presheafObjObjIso`.
-/
noncomputable def hom : (presheaf data G₀).obj (op (F.obj X₀)) ⟶ G₀.obj.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ (fun ⟨W₀, a, ha⟩ ↦
    presheafObjπ data G₀ _ (Sieve.ofArrows.i ha) ≫
      IsDenseSubsite.mapPreimage J F G₀ (Sieve.ofArrows.h ha)) (by
        rintro ⟨W₀, a, ha⟩ ⟨T₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
        have ha' := Sieve.ofArrows.fac ha
        have hb' := Sieve.ofArrows.fac hb
        dsimp at ha hb ha' hb' p₁ p₂ fac ⊢
        rw [assoc, assoc, IsDenseSubsite.mapPreimage_comp_map,
          IsDenseSubsite.mapPreimage_comp_map,
          ← restriction_eq_of_fac data G₀ (F.map (p₁ ≫ a))
            (F.map p₁ ≫ Sieve.ofArrows.h ha) (by rw [assoc, ha', map_comp]),
          restriction_eq_of_fac data G₀ (F.map (p₁ ≫ a))
            (F.map p₂ ≫ Sieve.ofArrows.h hb) (by rw [assoc, hb', fac, map_comp])])

variable {X₀}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.hom_ma
p** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSu
rj.presheafObjObjIso`。
形式化陈述：hom_map {W₀ : C₀} (a : W₀ ⟶ X₀) {i : (data (F.obj X₀)).I₀} (p : F.obj W₀ ⟶
 F.obj ((data (F.obj X₀)).X i)) (fac : p ≫ (data (F.obj X₀)).f i = F.map a) : ho
m data G₀ X₀ ≫ G₀.obj.map a.op = presheafObjπ data G₀ _ i ≫ IsDenseSubsite.mapPr
eimage J F G₀ p
参数：a : W₀ ⟶ X₀；data (F.obj X₀)；p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀)).X i)；fac 
: p ≫ (data (F.obj X₀)).f i = F.map a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.amalgamate_map`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} 
{A : Type u₂}   [inst_1 : CategoryTh…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_mapPre
image_condition`：presheafObj_mapPreimage_condition (X : C) (i₁ i₂ : (data X).I₀)
 {Y₀ : C₀} (p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((d…
· 使用定理 `CategoryTheory.Sieve.ofArrows.fac`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i ⟶ X
}   {W : C} {g : W ⟶ X}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma hom_map {W₀ : C₀} (a : W₀ ⟶ X₀) {i : (data (F.obj X₀)).I₀}
    (p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀)).X i))
    (fac : p ≫ (data (F.obj X₀)).f i = F.map a) :
    hom data G₀ X₀ ≫ G₀.obj.map a.op =
      presheafObjπ data G₀ _ i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  have ha : Sieve.functorPullback F (data (F.obj X₀)).toPreOneHypercover.sieve₀ a :=
    ⟨_, p, _, ⟨i⟩, fac⟩
  exact (G₀.2.amalgamate_map _ _ _ ⟨W₀, a, ha⟩).trans
    (presheafObj_mapPreimage_condition _ _ _ _ _ _ _
      ((Sieve.ofArrows.fac ha).trans fac.symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.hom_ma
pPreimage** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseDa
ta.essSurj.presheafObjObjIso`。
形式化陈述：hom_mapPreimage {W₀ : C₀} (a : F.obj W₀ ⟶ F.obj X₀) {i : (data (F.obj X₀))
.I₀} (p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀)).X i)) (fac : p ≫ (data (F.obj X₀))
.f i = a) : hom data G₀ X₀ ≫ IsDenseSubsite.mapPreimage J F G₀ a = presheafObjπ 
data G₀ _ i ≫ IsDenseSubsite.mapPreimage J F G₀ p
参数：a : F.obj W₀ ⟶ F.obj X₀；data (F.obj X₀)；p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀
)).X i)；fac : p ≫ (data (F.obj X₀)).f i = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp_map`：mapPreimage_
comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : Z ⟶ X) : mapPreimage K G F f ≫
 F.obj.map g.op = mapPreimage K G F (G.map g ≫ f…
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage.congr_simp`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} D] {J : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map`：mapPreimage_map {
X Y : C} (f : X ⟶ Y) : mapPreimage K G F (G.map f) = F.obj.map f.op
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.
hom_map`：hom_map {W₀ : C₀} (a : W₀ ⟶ X₀) {i : (data (F.obj X₀)).I₀} (p : F.obj W
₀ ⟶ F.obj ((data (F.obj X₀)).X i)) (fac : p ≫ (data (F.obj X₀)).f i =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_mapPreimage {W₀ : C₀} (a : F.obj W₀ ⟶ F.obj X₀) {i : (data (F.obj X₀)).I₀}
    (p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀)).X i))
    (fac : p ≫ (data (F.obj X₀)).f i = a) :
    hom data G₀ X₀ ≫ IsDenseSubsite.mapPreimage J F G₀ a =
      presheafObjπ data G₀ _ i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F a⟩ _ _ ?_
  rintro ⟨T₀, b, ⟨c, hc⟩⟩
  dsimp
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map, ← hc,
    IsDenseSubsite.mapPreimage_map]
  exact hom_map data G₀ c _ (by simp only [assoc, fac, hc])

variable (X₀)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `OneHypercoverDenseData.essSurj.presheafObjObjIso`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.inv** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.p
resheafObjObjIso`。
形式化陈述：inv : G₀.obj.obj (op X₀) ⟶ (presheaf data G₀).obj (op (F.obj X₀))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `OneHypercoverDenseData.essSurj.presheafObjObjIso`.
-/
noncomputable def inv : G₀.obj.obj (op X₀) ⟶ (presheaf data G₀).obj (op (F.obj X₀)) :=
  Multiequalizer.lift _ _
    (fun i ↦ IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀)).f i)) (by
      intro ⟨⟨i, i'⟩, j⟩
      simp [IsDenseSubsite.mapPreimage_comp_map, (data (F.obj X₀)).w j])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.inv_**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.
presheafObjObjIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_π (i : (data (F.obj X₀)).I₀) :
    inv data G₀ X₀ ≫ presheafObjπ data G₀ (F.obj X₀) i =
      IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀)).f i) :=
  Multiequalizer.lift_ι _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.inv_re
striction** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseDa
ta.essSurj.presheafObjObjIso`。
形式化陈述：inv_restriction {Y₀ : C₀} (f : F.obj Y₀ ⟶ F.obj X₀) : inv data G₀ X₀ ≫ res
triction data G₀ f = IsDenseSubsite.mapPreimage J F G₀ f
参数：f : F.obj Y₀ ⟶ F.obj X₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsCocontinuous`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.mem₀`：∀ {C₀ : Type u₀} {C 
: Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_map`：r
estriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀} (g : Y₀ ⟶ X₀) {i :
 (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i)) (fac : …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.
inv_π_assoc`：∀ {C₀ : Type u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, 
u₀} C₀] [inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp`：mapPreimage_comp
 {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : G.obj Y ⟶ G.obj Z) : mapPreimage K G F
 (f ≫ g) = mapPreimage K G F g ≫ mapPreimage…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp_map`：mapPreimage_
comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : Z ⟶ X) : mapPreimage K G F f ≫
 F.obj.map g.op = mapPreimage K G F (G.map g ≫ f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma inv_restriction {Y₀ : C₀} (f : F.obj Y₀ ⟶ F.obj X₀) :
    inv data G₀ X₀ ≫ restriction data G₀ f =
      IsDenseSubsite.mapPreimage J F G₀ f := by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F f⟩ _ _ ?_
  rintro ⟨W₀, a, b, fac₁⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.pullback_stable b (cover_lift F J₀ _ (data (F.obj X₀)).mem₀)⟩ _ _ ?_
  rintro ⟨T₀, c, _, d, _, ⟨i⟩, fac₂⟩
  dsimp at i d fac₂ ⊢
  simp only [assoc, ← Functor.map_comp, ← op_comp]
  rw [restriction_map data G₀ f (c ≫ a) d
    (by rw [fac₂, map_comp, map_comp_assoc, fac₁]), inv_π_assoc,
    ← IsDenseSubsite.mapPreimage_comp, fac₂,
    IsDenseSubsite.mapPreimage_comp_map J F G₀, map_comp,
      map_comp_assoc, fac₁]

end presheafObjObjIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf `presheaf data G₀` extends `G₀`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：presheafObjObjIso (X₀ : C₀) : (presheaf data G₀).obj (op (F.obj X₀)) ≅ G₀.
obj.obj (op X₀) where hom
参数：X₀ : C₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf `presheaf data G₀` extends `G₀`.
-/
noncomputable def presheafObjObjIso (X₀ : C₀) :
    (presheaf data G₀).obj (op (F.obj X₀)) ≅ G₀.obj.obj (op X₀) where
  hom := presheafObjObjIso.hom data G₀ X₀
  inv := presheafObjObjIso.inv data G₀ X₀
  hom_inv_id := presheafObj_hom_ext fun i ↦ by
    rw [assoc, presheafObjObjIso.inv_π, id_comp,
      presheafObjObjIso.hom_mapPreimage data G₀ _ (𝟙 _) (fac := by simp),
      IsDenseSubsite.mapPreimage_id, comp_id]
  inv_hom_id := by
    refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ _ _ ?_
    rintro ⟨Y₀, a, X, b, c, ⟨i⟩, fac⟩
    dsimp at i b fac ⊢
    simp [presheafObjObjIso.hom_map data G₀ _ b fac, ← IsDenseSubsite.mapPreimage_comp, fac]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_presheafObjO
bjIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseDa
ta.essSurj`。
形式化陈述：presheafMap_presheafObjObjIso_hom (X : C) (i : (data X).I₀) : presheafMap 
data G₀ ((data X).f i) ≫ (presheafObjObjIso data G₀ ((data X).X i)).hom = preshe
afObjπ data G₀ X i
参数：X : C；i : (data X).I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_hom_ex
t`：presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X} (h : fo
rall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ pres…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_π`：pre
sheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) : presheafMap data G₀ f ≫ pre
sheafObjπ data G₀ X i = restriction data G₀ ((data X).f i…
· 使用定理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.
eq_1`：∀ {C₀ : Type u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀]
 [inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.
inv_π`：inv_π (i : (data (F.obj X₀)).I₀) : inv data G₀ X₀ ≫ presheafObjπ data G₀ 
(F.obj X₀) i = IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀))…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.restriction_eq_of_
fac`：restriction_eq_of_fac {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {i : (data X).I₀
} (p : F.obj X₀ ⟶ F.obj ((data X).X i)) (fac : p ≫ (data X).f i =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma presheafMap_presheafObjObjIso_hom (X : C) (i : (data X).I₀) :
    presheafMap data G₀ ((data X).f i) ≫ (presheafObjObjIso data G₀ ((data X).X i)).hom =
      presheafObjπ data G₀ X i := by
  rw [← cancel_mono (presheafObjObjIso data G₀ ((data X).X i)).inv, assoc, Iso.hom_inv_id,
    comp_id]
  apply presheafObj_hom_ext
  intro j
  rw [assoc, presheafMap_π, presheafObjObjIso, presheafObjObjIso.inv_π data G₀]
  apply restriction_eq_of_fac
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso_inv_na
turality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseDat
a.essSurj`。
形式化陈述：presheafObjObjIso_inv_naturality {X₀ Y₀ : C₀} (f : X₀ ⟶ Y₀) : G₀.obj.map f
.op ≫ (presheafObjObjIso data G₀ X₀).inv = (presheafObjObjIso data G₀ Y₀).inv ≫ 
presheafMap data G₀ (F.map f)
参数：f : X₀ ⟶ Y₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObj_hom_ex
t`：presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X} (h : fo
rall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ pres…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.
inv_π`：inv_π (i : (data (F.obj X₀)).I₀) : inv data G₀ X₀ ≫ presheafObjπ data G₀ 
(F.obj X₀) i = IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀))…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_π`：pre
sheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) : presheafMap data G₀ f ≫ pre
sheafObjπ data G₀ X i = restriction data G₀ ((data X).f i…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafObjObjIso.
inv_restriction`：inv_restriction {Y₀ : C₀} (f : F.obj Y₀ ⟶ F.obj X₀) : inv data 
G₀ X₀ ≫ restriction data G₀ f = IsDenseSubsite.mapPreimage J F G₀ f
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp`：mapPreimage_comp
 {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : G.obj Y ⟶ G.obj Z) : mapPreimage K G F
 (f ≫ g) = mapPreimage K G F g ≫ mapPreimage…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map`：mapPreimage_map {
X Y : C} (f : X ⟶ Y) : mapPreimage K G F (G.map f) = F.obj.map f.op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma presheafObjObjIso_inv_naturality {X₀ Y₀ : C₀} (f : X₀ ⟶ Y₀) :
    G₀.obj.map f.op ≫ (presheafObjObjIso data G₀ X₀).inv =
      (presheafObjObjIso data G₀ Y₀).inv ≫ presheafMap data G₀ (F.map f) := by
  apply presheafObj_hom_ext
  intro j
  simp [presheafObjObjIso, IsDenseSubsite.mapPreimage_comp]


set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf `presheaf data G₀` extends `G₀`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.compPresheafIso** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：compPresheafIso : F.op ⋙ presheaf data G₀ ≅ G₀.obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf `presheaf data G₀` extends `G₀`.
-/
noncomputable def compPresheafIso : F.op ⋙ presheaf data G₀ ≅ G₀.obj :=
  (NatIso.ofComponents (fun _ ↦ (presheafObjObjIso data G₀ _).symm)
    (fun f ↦ presheafObjObjIso_inv_naturality data G₀ f.unop)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.isSheaf** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：isSheaf : Presheaf.IsSheaf J (presheaf data G₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.isSheaf_iff`：isSheaf_iff (
data : forall X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A) : Presheaf.IsShe
af J G ↔ Presheaf.IsSheaf J₀ (F.op ⋙ G) ∧ foral…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.presheafMap_preshe
afObjObjIso_hom`：presheafMap_presheafObjObjIso_hom (X : C) (i : (data X).I₀) : p
resheafMap data G₀ ((data X).f i) ≫ (presheafObjObjIso data G₀ ((data X).X i)…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSheaf : Presheaf.IsSheaf J (presheaf data G₀) := by
  rw [isSheaf_iff data]
  constructor
  · exact (Presheaf.isSheaf_of_iso_iff (compPresheafIso data G₀)).2 G₀.property
  · intro X
    refine ⟨(IsLimit.postcomposeHomEquiv
      (WalkingMulticospan.functorExt
          (fun _ ↦ presheafObjObjIso _ _ _) (fun _ ↦ presheafObjObjIso _ _ _)
          (fun _ ↦ (compPresheafIso _ _).hom.naturality _)
          (fun _ ↦ (compPresheafIso _ _).hom.naturality _)) _).1
      (IsLimit.ofIsoLimit (presheafObjIsLimit data G₀ X)
        (Multifork.ext (Iso.refl _) (fun i ↦ ?_)))⟩
    simp [Multifork.ι, PreOneHypercover.multifork, MulticospanIndex.multicospan]

/-- Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀ J X`
be a family of structures. Let `G₀` be a sheaf on `C₀`. This is a sheaf on `C` which
extends `G₀` (see `OneHypercoverDenseData.essSurj.isSheafIso`). -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.sheaf** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：sheaf : Sheaf J A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj.isSheaf`：isSheaf :
 Presheaf.IsSheaf J (presheaf data G₀)

--- 原说明 ---
Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀
 J X`
be a family of structures. Let `G₀` be a sheaf on `C₀`. This is a sheaf on `C` w
hich
extends `G₀` (see `OneHypercoverDenseData.essSurj.isSheafIso`).
-/
noncomputable def sheaf : Sheaf J A := ⟨presheaf data G₀, isSheaf data G₀⟩

/-- The sheaf `sheaf data G₀` extends `G₀`. -/
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj.sheafIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`。
形式化陈述：sheafIso : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…

--- 原说明 ---
The sheaf `sheaf data G₀` extends `G₀`.
-/
noncomputable def sheafIso : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀ :=
  (fullyFaithfulSheafToPresheaf J₀ A).preimageIso (compPresheafIso data G₀)

end essSurj

variable (A)

include data in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.essSurj** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：essSurj : EssSurj (sheafPushforwardContinuous F A J₀ J) where mem_essImage
 G₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
-/
lemma essSurj : EssSurj (sheafPushforwardContinuous F A J₀ J) where
  mem_essImage G₀ := ⟨_, ⟨essSurj.sheafIso data G₀⟩⟩

include data in
/-
**CategoryTheory.Functor.OneHypercoverDenseData.isEquivalence** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor.OneHypercoverDenseData`。
形式化陈述：isEquivalence : IsEquivalence (sheafPushforwardContinuous F A J₀ J) where 
essSurj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.essSurj`：essSurj : EssSurj
 (sheafPushforwardContinuous F A J₀ J) where mem_essImage G₀
-/
lemma isEquivalence : IsEquivalence (sheafPushforwardContinuous F A J₀ J) where
  essSurj := essSurj A data

end

end OneHypercoverDenseData

variable (A)

/-
**CategoryTheory.Functor.isEquivalence_of_isOneHypercoverDense** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isEquivalence_of_isOneHypercoverDense [HasLimitsOfSize.{w, w} A] [IsOneHyp
ercoverDense.{w} F J₀ J] : IsEquivalence (sheafPushforwardContinuous F A J₀ J)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.OneHypercoverDenseData.isEquivalence`：isEquivalen
ce : IsEquivalence (sheafPushforwardContinuous F A J₀ J) where essSurj
-/
lemma isEquivalence_of_isOneHypercoverDense
    [HasLimitsOfSize.{w, w} A] [IsOneHypercoverDense.{w} F J₀ J] :
    IsEquivalence (sheafPushforwardContinuous F A J₀ J) :=
  OneHypercoverDenseData.isEquivalence.{w} A (oneHypercoverDenseData F J₀ J)

end Functor

end CategoryTheory

