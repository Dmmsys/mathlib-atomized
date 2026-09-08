/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# The site induced by a morphism property

Let `C` be a category with pullbacks and `P` be a multiplicative morphism property which is
stable under base change. Then `P` induces a pretopology, where coverings are given by presieves
whose elements satisfy `P`.

Standard examples of pretopologies in algebraic geometry, such as the étale site, are obtained from
this construction by intersecting with the pretopology of surjective families.

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

namespace MorphismProperty

variable {P Q : MorphismProperty C}

/-- This is the precoverage on `C` where covering presieves are those where every
morphism satisfies `P`. -/
/-
**CategoryTheory.MorphismProperty.precoverage** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：precoverage (P : MorphismProperty C) : Precoverage C where coverings X
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the precoverage on `C` where covering presieves are those where every
morphism satisfies `P`.
-/
def precoverage (P : MorphismProperty C) : Precoverage C where
  coverings X := {S | ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → P f}

@[simp]
/-
**CategoryTheory.MorphismProperty.ofArrows_mem_precoverage** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：ofArrows_mem_precoverage {X : C} {ι : Type*} {Y : ι -> C} {f : forall i, Y
 i ⟶ X} : .ofArrows Y f in precoverage P X ↔ forall i, P (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofArrows_mem_precoverage {X : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} :
    .ofArrows Y f ∈ precoverage P X ↔ ∀ i, P (f i) :=
  ⟨fun h i ↦ h ⟨i⟩, fun h _ g ⟨i⟩ ↦ h i⟩

@[simp, grind =]
/-
**CategoryTheory.MorphismProperty.singleton_mem_precoverage** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：singleton_mem_precoverage {X Y : C} (f : X ⟶ Y) : .singleton f in precover
age P Y ↔ P f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_pUnit`：ofArrows_pUnit : (ofArrows _ fun
 _ : PUnit.{w + 1} => f) = singleton f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma singleton_mem_precoverage {X Y : C} (f : X ⟶ Y) :
    .singleton f ∈ precoverage P Y ↔ P f := by
  simp [← Presieve.ofArrows_pUnit.{0}]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] [P.RespectsIso] : P.precoverage.HasIsos where
  mem_coverings_of_isIso f _ _ _ := fun ⟨⟩ ↦ P.of_isIso f
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderBaseChange] : P.precoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf T g W p₁ p₂ h Z g hg := by
    obtain ⟨i⟩ := hg
    exact P.of_isPullback (h i).flip (hf ⟨i⟩)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderComposition] : P.precoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg Z p := by
    intro ⟨i⟩
    exact P.comp_mem _ _ (hg _ ⟨i.2⟩) (hf ⟨i.1⟩)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Precoverage.Small.{w} P.precoverage where
  zeroHypercoverSmall E := by
    constructor
    use PEmpty, PEmpty.elim
    simp
/-
**CategoryTheory.MorphismProperty.precoverage_monotone** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：precoverage_monotone (hPQ : P <= Q) : precoverage P <= precoverage Q
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma precoverage_monotone (hPQ : P ≤ Q) : precoverage P ≤ precoverage Q :=
  fun _ _ hR _ _ hg ↦ hPQ _ (hR hg)

variable (P Q) in
/-
**CategoryTheory.MorphismProperty.precoverage_inf** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：precoverage_inf : precoverage (P ⊓ Q) = precoverage P ⊓ precoverage Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ext`：∀ {C : Type u_1} {inst : CategoryTheory.
Category.{v_1, u_1} C} {x y : CategoryTheory.Precoverage C},   x.coverings = y.c
overings → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma precoverage_inf : precoverage (P ⊓ Q) = precoverage P ⊓ precoverage Q := by
  ext X R
  exact ⟨fun hS ↦ ⟨fun _ _ hf ↦ (hS hf).left, fun _ _ hf ↦ (hS hf).right⟩,
    fun h ↦ fun _ _ hf ↦ ⟨h.left hf, h.right hf⟩⟩

@[simp, grind .]
/-
**CategoryTheory.MorphismProperty.bot_mem_precoverage** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：bot_mem_precoverage (X : C) : ⊥ in precoverage P X
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bot_mem_precoverage (X : C) : ⊥ ∈ precoverage P X := fun _ _ h ↦ h.elim
/-
**CategoryTheory.MorphismProperty.comap_precoverage** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：comap_precoverage {D : Type*} [Category* D] (P : MorphismProperty D) (F : 
C ⥤ D) : P.precoverage.comap F = (P.inverseImage F).precoverage
参数：P : MorphismProperty D；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ext`：∀ {C : Type u_1} {inst : CategoryTheory.
Category.{v_1, u_1} C} {x y : CategoryTheory.Precoverage C},   x.coverings = y.c
overings → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `CategoryTheory.Presieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Pres
ieve X) : exists (ι : Type (max u₁ v₁)) (Y : ι -> C) (f : forall i, Y i ⟶ X), R 
= .ofArrows Y f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma comap_precoverage {D : Type*} [Category* D] (P : MorphismProperty D) (F : C ⥤ D) :
    P.precoverage.comap F = (P.inverseImage F).precoverage := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

/-- If `P` is stable under base change, this is the coverage on `C` where covering presieves
are those where every morphism satisfies `P`. -/
@[simps toPrecoverage]
/-
**CategoryTheory.MorphismProperty.coverage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：coverage (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullba
cks] : Coverage C where __
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under base change, this is the coverage on `C` where covering p
resieves
are those where every morphism satisfies `P`.
-/
def coverage (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks] :
    Coverage C where
  __ := precoverage P
  pullback X Y f S hS := by
    have : S.HasPullbacks f := ⟨fun {W} h hh ↦ P.hasPullback _ (hS hh)⟩
    refine ⟨S.pullbackArrows f, ?_, .pullbackArrows f S⟩
    intro Z g ⟨W, a, h⟩
    have := S.hasPullback f h
    exact P.pullback_snd _ _ (hS h)

/-- If `P` is stable under base change, it induces a Grothendieck topology: the one associated
to `coverage P`. -/
/-
**CategoryTheory.MorphismProperty.grothendieckTopology** 是 Mathlib 中的一个缩写定义，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：grothendieckTopology (P : MorphismProperty C) [P.IsStableUnderBaseChange] 
[P.HasPullbacks] : GrothendieckTopology C
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under base change, it induces a Grothendieck topology: the one 
associated
to `coverage P`.
-/
abbrev grothendieckTopology (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks] :
    GrothendieckTopology C :=
  P.coverage.toGrothendieck

section HasPullbacks

variable [P.IsStableUnderBaseChange] [HasPullbacks C]

/-- If `P` is a multiplicative morphism property which is stable under base change on a category
`C` with pullbacks, then `P` induces a pretopology, where coverings are given by presieves whose
elements satisfy `P`. -/
@[simps! toPrecoverage]
/-
**CategoryTheory.MorphismProperty.pretopology** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：pretopology (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnder
BaseChange] : Pretopology C
参数：P : MorphismProperty C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangePrecoverageOf
IsStableUnderBaseChange`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} C] {P : CategoryTheory.MorphismProperty C}   [P.IsStableUnderBaseChange], P
.prec…

--- 原说明 ---
If `P` is a multiplicative morphism property which is stable under base change o
n a category
`C` with pullbacks, then `P` induces a pretopology, where coverings are given by
 presieves whose
elements satisfy `P`.
-/
def pretopology (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange] :
    Pretopology C :=
  (precoverage P).toPretopology

/-- If `P` is also multiplicative, the coverage induced by `P` is the pretopology induced by `P`. -/
/-
**CategoryTheory.MorphismProperty.coverage_eq_toCoverage_pretopology** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：coverage_eq_toCoverage_pretopology [P.IsMultiplicative] : P.coverage = P.p
retopology.toCoverage
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…

--- 原说明 ---
If `P` is also multiplicative, the coverage induced by `P` is the pretopology in
duced by `P`.
-/
lemma coverage_eq_toCoverage_pretopology [P.IsMultiplicative] :
    P.coverage = P.pretopology.toCoverage := rfl

/-- If `P` is also multiplicative, the topology induced by `P` is the topology induced by the
pretopology induced by `P`. -/
/-
**CategoryTheory.MorphismProperty.grothendieckTopology_eq_toGrothendieck_pretopo
logy** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：grothendieckTopology_eq_toGrothendieck_pretopology [P.IsMultiplicative] : 
P.grothendieckTopology = P.pretopology.toGrothendieck
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.grothendieckTopology.eq_1`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.MorphismPr
operty C)   [inst_1 : P.IsStableUnderBaseChange…
· 使用引理 `CategoryTheory.MorphismProperty.coverage_eq_toCoverage_pretopology`：cove
rage_eq_toCoverage_pretopology [P.IsMultiplicative] : P.coverage = P.pretopology
.toCoverage
· 使用定理 `CategoryTheory.Pretopology.toGrothendieck_toCoverage`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Has
Pullbacks C]   (J : CategoryTheory.Pretopo…

--- 原说明 ---
If `P` is also multiplicative, the topology induced by `P` is the topology induc
ed by the
pretopology induced by `P`.
-/
lemma grothendieckTopology_eq_toGrothendieck_pretopology [P.IsMultiplicative] :
    P.grothendieckTopology = P.pretopology.toGrothendieck := by
  rw [grothendieckTopology, coverage_eq_toCoverage_pretopology,
    Pretopology.toGrothendieck_toCoverage]

section

variable {P Q : MorphismProperty C}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-
**CategoryTheory.MorphismProperty.pretopology_monotone** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：pretopology_monotone (hPQ : P <= Q) : P.pretopology <= Q.pretopology
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.precoverage_monotone`：precoverage_monoto
ne (hPQ : P <= Q) : precoverage P <= precoverage Q
-/
lemma pretopology_monotone (hPQ : P ≤ Q) : P.pretopology ≤ Q.pretopology :=
  precoverage_monotone hPQ

variable (P Q) in
/-
**CategoryTheory.MorphismProperty.pretopology_inf** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：pretopology_inf : (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretopology.ext`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {inst_1 : CategoryTheory.Limits.HasPullbacks C}   {x y : Catego
ryTheory.Pretopology…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.inf`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProperty C}
 [P.IsMultiplicative]   [Q.IsMultiplicativ…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MorphismProperty.pretopology_toPrecoverage`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limit
s.HasPullbacks C]   (P : CategoryTheory.Morphis…
· 使用引理 `CategoryTheory.MorphismProperty.precoverage_inf`：precoverage_inf : preco
verage (P ⊓ Q) = precoverage P ⊓ precoverage Q
-/
lemma pretopology_inf : (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology := by
  ext : 1
  simp only [pretopology_toPrecoverage, precoverage_inf]
  rfl

end

end HasPullbacks

end MorphismProperty

/-- The weakest morphism property satisfied by all morphisms in covering families. -/
/-
**CategoryTheory.Precoverage.morphismProperty** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Precoverage`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.Precoverage C → CategoryTheory.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weakest morphism property satisfied by all morphisms in covering families.
-/
def Precoverage.morphismProperty (K : Precoverage C) : MorphismProperty C :=
  fun _ Y f ↦ ∃ R ∈ K Y, R f

@[simp]
/-
**CategoryTheory.MorphismProperty.morphismProperty_precoverage** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.MorphismProperty C),   P.precoverage.morphismProperty = P
参数：P : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma MorphismProperty.morphismProperty_precoverage (P : MorphismProperty C) :
    P.precoverage.morphismProperty = P := by
  ext X Y f
  exact ⟨fun ⟨R, hR, hf⟩ ↦ hR hf, fun hf ↦ ⟨.singleton f, by simpa⟩⟩

namespace Precoverage

variable {K L : Precoverage C} {P : MorphismProperty C}

/-
**CategoryTheory.Precoverage.morphismProperty_le_iff_le_precoverage** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Precoverage`。
形式化陈述：morphismProperty_le_iff_le_precoverage : K.morphismProperty <= P ↔ K <= P.
precoverage
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma morphismProperty_le_iff_le_precoverage :
    K.morphismProperty ≤ P ↔ K ≤ P.precoverage :=
  ⟨fun hle _ R hR _ _ hf ↦ hle _ ⟨R, hR, hf⟩, fun hle _ _ _ ⟨_, hR, hf⟩ ↦ hle _ hR hf⟩
/-
**CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Precoverage`。
形式化陈述：galoisConnection_morphismProperty_precoverage : GaloisConnection (Precover
age.morphismProperty (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.morphismProperty_le_iff_le_precoverage`：morph
ismProperty_le_iff_le_precoverage : K.morphismProperty <= P ↔ K <= P.precoverage
-/
lemma galoisConnection_morphismProperty_precoverage :
    GaloisConnection (Precoverage.morphismProperty (C := C)) MorphismProperty.precoverage :=
  @Precoverage.morphismProperty_le_iff_le_precoverage _ _
/-
**CategoryTheory.Precoverage.monotone_morphismProperty** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Precoverage`。
形式化陈述：monotone_morphismProperty : Monotone (Precoverage.morphismProperty (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用引理 `CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage
`：galoisConnection_morphismProperty_precoverage : GaloisConnection (Precoverage.
morphismProperty (C
-/
lemma monotone_morphismProperty : Monotone (Precoverage.morphismProperty (C := C)) :=
  Precoverage.galoisConnection_morphismProperty_precoverage.monotone_l
/-
**CategoryTheory.Precoverage.le_precoverage_morphismProperty** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Precoverage`。
形式化陈述：le_precoverage_morphismProperty : K <= K.morphismProperty.precoverage
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用引理 `CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage
`：galoisConnection_morphismProperty_precoverage : GaloisConnection (Precoverage.
morphismProperty (C
-/
lemma le_precoverage_morphismProperty : K ≤ K.morphismProperty.precoverage :=
  galoisConnection_morphismProperty_precoverage.le_u_l _

@[simp]
/-
**CategoryTheory.Precoverage.morphismProperty_bot** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Precoverage`。
形式化陈述：morphismProperty_bot : (⊥ : Precoverage C).morphismProperty = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage
`：galoisConnection_morphismProperty_precoverage : GaloisConnection (Precoverage.
morphismProperty (C
-/
lemma morphismProperty_bot : (⊥ : Precoverage C).morphismProperty = ⊥ :=
  Precoverage.galoisConnection_morphismProperty_precoverage.l_bot

@[simp]
/-
**CategoryTheory.Precoverage.morphismProperty_sup** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Precoverage`。
形式化陈述：morphismProperty_sup : (K ⊔ L).morphismProperty = K.morphismProperty ⊔ L.m
orphismProperty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage
`：galoisConnection_morphismProperty_precoverage : GaloisConnection (Precoverage.
morphismProperty (C
-/
lemma morphismProperty_sup : (K ⊔ L).morphismProperty = K.morphismProperty ⊔ L.morphismProperty :=
  Precoverage.galoisConnection_morphismProperty_precoverage.l_sup
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.HasIsos] : K.morphismProperty.ContainsIdentities where
  id_mem X := ⟨.singleton (𝟙 X), K.mem_coverings_of_isIso _, by simp⟩

@[simp, grind .]
/-
**CategoryTheory.Precoverage.ZeroHypercover.morphismProperty** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Precoverage.ZeroHypercover`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {K : Catego
ryTheory.Precoverage C} {X : C}   {E : K.ZeroHypercover X} (i : E.I₀), K.morphis
mProperty (E.f i)
参数：i : E.I₀；E.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma ZeroHypercover.morphismProperty {X : C} {E : ZeroHypercover.{w} K X} (i : E.I₀) :
    K.morphismProperty (E.f i) :=
  ⟨_, E.mem₀, ⟨i⟩⟩

end Precoverage

@[simp]
/-
**CategoryTheory.MorphismProperty.precoverage_top** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C], ⊤.precover
age = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用引理 `CategoryTheory.Precoverage.galoisConnection_morphismProperty_precoverage
`：galoisConnection_morphismProperty_precoverage : GaloisConnection (Precoverage.
morphismProperty (C
-/
lemma MorphismProperty.precoverage_top : (⊤ : MorphismProperty C).precoverage = ⊤ :=
  Precoverage.galoisConnection_morphismProperty_precoverage.u_top

end CategoryTheory

