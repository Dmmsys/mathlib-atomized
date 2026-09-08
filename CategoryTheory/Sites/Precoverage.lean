/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Pullbacks
public import Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!

# Precoverages

A precoverage `K` on a category `C` is a set of presieves associated to every object `X : C`,
called "covering presieves".
There are no conditions on this set. Common extensions of a precoverage are:

- `CategoryTheory.Coverage`: A coverage is a precoverage that satisfies a pullback compatibility
  condition, saying that whenever `S` is a covering presieve on `X` and `f : Y ⟶ X` is a morphism,
  then there exists some covering sieve `T` on `Y` such that `T` factors through `S` along `f`.
- `CategoryTheory.Pretopology`: If `C` has pullbacks, a pretopology on `C` is a precoverage that
  has isomorphisms and is stable under pullback and refinement.

These two are defined in later files. For precoverages, we define stability conditions:

- `CategoryTheory.Precoverage.HasIsos`: Singleton presieves by isomorphisms are covering.
- `CategoryTheory.Precoverage.IsStableUnderBaseChange`: The pullback of a covering presieve is again
  covering.
- `CategoryTheory.Precoverage.IsStableUnderComposition`: Refining a covering presieve by covering
  presieves yields a covering presieve.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

/-- A precoverage is a collection of *covering* presieves on every object `X : C`.
See `CategoryTheory.Coverage` and `CategoryTheory.Pretopology` for common extensions of this. -/
@[ext]
/-
**CategoryTheory.Precoverage** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Type (max u_1 v_
1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage is a collection of *covering* presieves on every object `X : C`.
See `CategoryTheory.Coverage` and `CategoryTheory.Pretopology` for common extens
ions of this.
-/
structure Precoverage (C : Type*) [Category* C] where
  /-- The collection of covering presieves for an object `X`. -/
  coverings : ∀ (X : C), Set (Presieve X)

namespace Precoverage

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Precoverage C) (fun _ => (X : C) → Set (Presieve X)) where
  coe := coverings
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Precoverage C) where
  le A B := A.coverings ≤ B.coverings
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 X := le_trans (h1 X) (h2 X)
  le_antisymm _ _ h1 h2 := Precoverage.ext <| funext <|
    fun X => le_antisymm (h1 X) (h2 X)
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Precoverage C) where
  min A B := ⟨A.coverings ⊓ B.coverings⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Precoverage C) where
  max A B := ⟨A.coverings ⊔ B.coverings⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (Precoverage C) where
  sSup A := ⟨⨆ K ∈ A, K.coverings⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Precoverage C) where
  sInf A := ⟨⨅ K ∈ A, K.coverings⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (Precoverage C) where
  top.coverings _ := .univ
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (Precoverage C) where
  bot.coverings _ := ∅
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Precoverage C) :=
  Function.Injective.completeLattice Precoverage.coverings (fun _ _ hab ↦ Precoverage.ext hab)
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

/-- A precoverage has isomorphisms if singleton presieves by isomorphisms are covering. -/
/-
**CategoryTheory.Precoverage.HasIsos** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Precoverage`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage has isomorphisms if singleton presieves by isomorphisms are coveri
ng.
-/
class HasIsos (J : Precoverage C) : Prop where
  mem_coverings_of_isIso {S T : C} (f : S ⟶ T) [IsIso f] : .singleton f ∈ J T

/-- A precoverage is stable under base change if pullbacks of covering presieves
are covering presieves.
Use `Precoverage.mem_coverings_of_isPullback` for less universe restrictions.
Note: This is stronger than the analogous requirement for a `Pretopology`, because
`IsPullback` does not imply equality with the (arbitrarily) chosen pullbacks in `C`. -/
/-
**CategoryTheory.Precoverage.IsStableUnderBaseChange** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.Precoverage`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage is stable under base change if pullbacks of covering presieves
are covering presieves.
Use `Precoverage.mem_coverings_of_isPullback` for less universe restrictions.
Note: This is stronger than the analogous requirement for a `Pretopology`, becau
se
`IsPullback` does not imply equality with the (arbitrarily) chosen pullbacks in 
`C`.
-/
class IsStableUnderBaseChange (J : Precoverage C) : Prop where
  mem_coverings_of_isPullback {ι : Type (max u v)} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (hR : Presieve.ofArrows X f ∈ J S) {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    .ofArrows P p₁ ∈ J Y

/-- A precoverage is stable under composition if the indexed composition
of coverings is again a covering.
Use `Precoverage.comp_mem_coverings` for less universe restrictions.
Note: This is stronger than the analogous requirement for a `Pretopology`, because
this is in general not equal to a `Presieve.bind`. -/
/-
**CategoryTheory.Precoverage.IsStableUnderComposition** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.Precoverage`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage is stable under composition if the indexed composition
of coverings is again a covering.
Use `Precoverage.comp_mem_coverings` for less universe restrictions.
Note: This is stronger than the analogous requirement for a `Pretopology`, becau
se
this is in general not equal to a `Presieve.bind`.
-/
class IsStableUnderComposition (J : Precoverage C) : Prop where
  comp_mem_coverings {ι : Type (max u v)}
    {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ J S)
    {σ : ι → Type (max u v)} {Y : ∀ (i : ι), σ i → C}
    (g : ∀ i j, Y i j ⟶ X i) (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ J (X i)) :
    .ofArrows (fun p : Σ i, σ i ↦ Y _ p.2) (fun _ ↦ g _ _ ≫ f _) ∈ J S

/-- A precoverage is stable under `⊔` if whenever `R` and `S` are coverings,
also `R ⊔ S` is a covering. -/
/-
**CategoryTheory.Precoverage.IsStableUnderSup** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Precoverage`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage is stable under `⊔` if whenever `R` and `S` are coverings,
also `R ⊔ S` is a covering.
-/
class IsStableUnderSup (J : Precoverage C) where
  sup_mem_coverings {X : C} {R S : Presieve X} (hR : R ∈ J X) (hS : S ∈ J X) :
    R ⊔ S ∈ J X

/-- A precoverage has pullbacks, if every covering presieve has pullbacks along arbitrary
morphisms. -/
/-
**CategoryTheory.Precoverage.HasPullbacks** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheo
ry.Precoverage`。
形式化陈述：HasPullbacks (J : Precoverage C) where hasPullbacks_of_mem {X Y : C} {R : 
Presieve Y} (f : X ⟶ Y) (hR : R in J Y) : R.HasPullbacks f  alias mem_coverings_
of_isIso
参数：J : Precoverage C；f : X ⟶ Y；hR : R in J Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage has pullbacks, if every covering presieve has pullbacks along arbi
trary
morphisms.
-/
class HasPullbacks (J : Precoverage C) where
  hasPullbacks_of_mem {X Y : C} {R : Presieve Y} (f : X ⟶ Y) (hR : R ∈ J Y) : R.HasPullbacks f

alias mem_coverings_of_isIso := HasIsos.mem_coverings_of_isIso
alias sup_mem_coverings := IsStableUnderSup.sup_mem_coverings
alias hasPullbacks_of_mem := HasPullbacks.hasPullbacks_of_mem

set_option backward.isDefEq.respectTransparency.types false in
set_option warning.simp.varHead false in
attribute [local simp] Presieve.ofArrows.obj_idx Presieve.ofArrows.hom_idx in
/-
**CategoryTheory.Precoverage.mem_coverings_of_isPullback** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Precoverage`。
形式化陈述：mem_coverings_of_isPullback {J : Precoverage C} [IsStableUnderBaseChange J
] {ι : Type w} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hR : Presieve.ofArr
ows X f in J S) {Y : C} (g : Y ⟶ S) {P : ι -> C} (p₁ : forall i, P i ⟶ Y) (p₂ : 
forall i, P i ⟶ X i) (h : forall i, IsPullback (p₁ i) (p₂ i) g (f i)) : .ofArrow
s P p₁ in J Y
参数：f : forall i, X i ⟶ S；hR : Presieve.ofArrows X f in J S；g : Y ⟶ S；p₁ : forall
 i, P i ⟶ Y；p₂ : forall i, P i ⟶ X i；h : forall i, IsPullback (p₁ i) (p₂ i) g (f
 i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Presieve.ofArrows.mk'`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} {ι : Type u_1} {Y : ι → C} {f : (i : ι) → Y i 
⟶ X}   {Z : C} {g : Z ⟶ X}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.ofArrows.obj_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Presieve.ofArrows.hom_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPu
llback`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTh
eory.Precoverage C}   [self : J.IsStableUnderBaseChange] {ι : Type (…
-/
lemma mem_coverings_of_isPullback {J : Precoverage C} [IsStableUnderBaseChange J]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hR : Presieve.ofArrows X f ∈ J S) {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    .ofArrows P p₁ ∈ J Y := by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` needs not be injective, the indexing type is a sum.
  let a (i : (Presieve.ofArrows X f).uncurry ⊕ (Presieve.ofArrows P p₁).uncurry) : ι :=
    i.elim (fun i ↦ i.2.idx) (fun i ↦ i.2.idx)
  convert_to Presieve.ofArrows (P ∘ a) (fun i ↦ p₁ (a i)) ∈ _
  · refine le_antisymm (fun Z g hg ↦ ?_) fun Z g ⟨i⟩ ↦ ⟨a i⟩
    exact .mk' (Sum.inr ⟨⟨_, _⟩, hg⟩) (by cat_disch) (by cat_disch)
  · refine IsStableUnderBaseChange.mem_coverings_of_isPullback (fun i ↦ f (a i)) ?_ g _
      (fun i ↦ p₂ (a i)) fun i ↦ h _
    convert! hR
    refine le_antisymm (fun Z g ⟨i⟩ ↦ .mk _) fun Z g hg ↦ ?_
    exact .mk' (Sum.inl ⟨⟨_, _⟩, hg⟩) (by cat_disch) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option warning.simp.varHead false in
attribute [local simp] Presieve.ofArrows.obj_idx Presieve.ofArrows.hom_idx in
/-
**CategoryTheory.Precoverage.comp_mem_coverings** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Precoverage`。
形式化陈述：comp_mem_coverings {J : Precoverage C} [IsStableUnderComposition J] {ι : T
ype w} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hf : Presieve.ofArrows X f 
in J S) {σ : ι -> Type w'} {Y : forall (i : ι), σ i -> C} (g : forall i j, Y i j
 ⟶ X i) (hg : forall i, Presieve.ofArrows (Y i) (g i) in J (X i)) : .ofArrows (f
un p : Σ i, σ i => Y _ p.2) (fun _ => g _ _ ≫ f _) in J S
参数：f : forall i, X i ⟶ S；hf : Presieve.ofArrows X f in J S；i : ι；g : forall i j,
 Y i j ⟶ X i；hg : forall i, Presieve.ofArrows (Y i) (g i) in J (X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Presieve.ofArrows.mk'`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} {ι : Type u_1} {Y : ι → C} {f : (i : ι) → Y i 
⟶ X}   {Z : C} {g : Z ⟶ X}…
· 使用定理 `CategoryTheory.Presieve.ofArrows.obj_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `CategoryTheory.Presieve.ofArrows.eq_eqToHom_comp_hom_idx`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C}
 {f : (i : ι) → X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `CategoryTheory.Precoverage.IsStableUnderComposition.comp_mem_coverings`：
∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.Pre
coverage C}   [self : J.IsStableUnderComposition] {ι : Type …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Presieve.ofArrows.hom_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma comp_mem_coverings {J : Precoverage C} [IsStableUnderComposition J] {ι : Type w}
    {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ J S)
    {σ : ι → Type w'} {Y : ∀ (i : ι), σ i → C}
    (g : ∀ i j, Y i j ⟶ X i) (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ J (X i)) :
    .ofArrows (fun p : Σ i, σ i ↦ Y _ p.2) (fun _ ↦ g _ _ ≫ f _) ∈ J S := by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` and `g` need not be injective, the indexing type is a sigma of sums.
  let ι' : Type (max u v) := (Presieve.ofArrows X f).uncurry
  let σ' (i : ι') : Type (max u v) := (Presieve.ofArrows (Y i.2.idx) (g i.2.idx)).uncurry
  let α : Type (max u v) :=
    (Presieve.ofArrows (fun p : Σ i, σ i ↦ Y _ p.2) (fun _ ↦ g _ _ ≫ f _)).uncurry
  let τ' (a : α) : Type (max u v) := (Presieve.ofArrows (Y a.2.idx.1) (g a.2.idx.1)).uncurry
  let fib (i : ι' ⊕ α) := i.elim (fun i ↦ σ' i) (fun i ↦ Unit ⊕ τ' i)
  let incl (p : ι' ⊕ α) : ι := p.elim (fun i ↦ i.2.idx) (fun i ↦ i.2.idx.1)
  let fibincl (i : ι' ⊕ α) (j : fib i) : σ (incl i) := match i with
    | .inl i => j.2.idx
    | .inr i => j.elim (fun _ ↦ i.2.idx.2) (fun i ↦ i.2.idx)
  convert_to Presieve.ofArrows _
      (fun p : Σ (i : ι' ⊕ α), fib i ↦ g (incl p.1) (fibincl _ p.2) ≫ f (incl p.1)) ∈ J.coverings S
  · refine le_antisymm (fun T u hu ↦ ?_) fun T u ⟨p⟩ ↦ .mk (Sigma.mk (incl p.1) (fibincl p.1 p.2))
    exact .mk' ⟨Sum.inr ⟨⟨_, _⟩, hu⟩, .inl ⟨⟩⟩ hu.obj_idx.symm hu.eq_eqToHom_comp_hom_idx
  · refine IsStableUnderComposition.comp_mem_coverings (f := fun i ↦ f (incl i))
        (g := fun i j ↦ g (incl i) (fibincl i j)) ?_ fun i ↦ ?_
    · convert! hf
      refine le_antisymm (fun T u ⟨p⟩ ↦ .mk _) fun T u hu ↦ ?_
      exact .mk' (Sum.inl ⟨⟨_, _⟩, hu⟩) (by cat_disch) (by cat_disch)
    · convert! hg (incl i)
      refine le_antisymm (fun T u ⟨p⟩ ↦ .mk _) fun T u hu ↦ ?_
      match i with
      | .inl i => exact .mk' ⟨⟨_, _⟩, hu⟩ (by cat_disch) (by cat_disch)
      | .inr i => exact .mk' (.inr ⟨⟨_, _⟩, hu⟩) (by cat_disch) (by cat_disch)
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Precoverage C) [Limits.HasPullbacks C] : J.HasPullbacks where
  hasPullbacks_of_mem := inferInstance
/-
**CategoryTheory.Precoverage.pullbackArrows_mem** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Precoverage`。
形式化陈述：pullbackArrows_mem {J : Precoverage C} [IsStableUnderBaseChange J] {X Y : 
C} (f : X ⟶ Y) {R : Presieve Y} (hR : R in J Y) [R.HasPullbacks f] : R.pullbackA
rrows f in J X
参数：f : X ⟶ Y；hR : R in J Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Pres
ieve X) : exists (ι : Type (max u₁ v₁)) (Y : ι -> C) (f : forall i, Y i ⟶ X), R 
= .ofArrows Y f
· 使用定理 `CategoryTheory.Presieve.hasPullback`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y : C} (f : Y 
⟶ X)   [self : R.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfArrowsOfHasPullback`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) {ι : Ty
pe u_1} (Z : ι → C)   (g : (i : ι) → Z i ⟶ X) [∀ (i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_pullback`：ofArrows_pullback {ι : Type*}
 (Z : ι -> C) (g : forall i : ι, Z i ⟶ X) [forall i, HasPullback (g i) f] : (ofA
rrows (fun i => pullback (g i) …
· 使用引理 `CategoryTheory.Precoverage.mem_coverings_of_isPullback`：mem_coverings_of
_isPullback {J : Precoverage C} [IsStableUnderBaseChange J] {ι : Type w} {S : C}
 {X : ι -> C} (f : forall i, X i ⟶ S) (hR : …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma pullbackArrows_mem {J : Precoverage C} [IsStableUnderBaseChange J]
    {X Y : C} (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ J Y) [R.HasPullbacks f] :
    R.pullbackArrows f ∈ J X := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : Limits.HasPullback (g i) f := Presieve.hasPullback f (Presieve.ofArrows.mk i)
  rw [← Presieve.ofArrows_pullback]
  exact mem_coverings_of_isPullback _ hR _ _ _ fun i ↦ (IsPullback.of_hasPullback _ _).flip
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J K : Precoverage C) [HasIsos J] [HasIsos K] : HasIsos (J ⊓ K) where
  mem_coverings_of_isIso f _ := ⟨mem_coverings_of_isIso f, mem_coverings_of_isIso f⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J K : Precoverage C) [IsStableUnderBaseChange J] [IsStableUnderBaseChange K] :
    IsStableUnderBaseChange (J ⊓ K) where
  mem_coverings_of_isPullback _ hf _ _ _ _ _ h :=
    ⟨mem_coverings_of_isPullback _ hf.1 _ _ _ h, mem_coverings_of_isPullback _ hf.2 _ _ _ h⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J K : Precoverage C) [IsStableUnderComposition J]
    [IsStableUnderComposition K] : IsStableUnderComposition (J ⊓ K) where
  comp_mem_coverings _ h _ _ _ H :=
    ⟨comp_mem_coverings _ h.1 _ fun i ↦ (H i).1, comp_mem_coverings _ h.2 _ fun i ↦ (H i).2⟩
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J K : Precoverage C) [IsStableUnderSup J] [IsStableUnderSup K] :
    IsStableUnderSup (J ⊓ K) where
  sup_mem_coverings hR hS := ⟨J.sup_mem_coverings hR.1 hS.1, K.sup_mem_coverings hR.2 hS.2⟩
/-
**CategoryTheory.Precoverage.hasPairwisePullbacks_of_mem** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Precoverage`。
形式化陈述：hasPairwisePullbacks_of_mem (J : Precoverage C) [J.HasPullbacks] {X : C} {
R : Presieve X} (hR : R in J X) : R.HasPairwisePullbacks where has_pullbacks h f
 _
参数：J : Precoverage C；hR : R in J X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.HasPullbacks.hasPullback`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y
 : C} (f : Y ⟶ X)   [self : R.HasPullb…
· 使用定理 `CategoryTheory.Precoverage.hasPullbacks_of_mem`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {J : CategoryTheory.Precoverage C} [self : J.Ha
sPullbacks]   {X Y : C} {R : Categor…
-/
lemma hasPairwisePullbacks_of_mem (J : Precoverage C) [J.HasPullbacks] {X : C} {R : Presieve X}
    (hR : R ∈ J X) :
    R.HasPairwisePullbacks where
  has_pullbacks h f _ := (J.hasPullbacks_of_mem f hR).hasPullback h

section Functoriality

variable {D : Type*} [Category* D] {F : C ⥤ D}

variable {J K : Precoverage D}

open Limits

/-- If `J` is a precoverage on `D`, we obtain a precoverage on `C` by declaring a presieve on `D`
to be covering if its image under `F` is. -/
/-
**CategoryTheory.Precoverage.comap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pre
coverage`。
形式化陈述：comap (F : C ⥤ D) (J : Precoverage D) : Precoverage C where coverings Y
参数：F : C ⥤ D；J : Precoverage D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is a precoverage on `D`, we obtain a precoverage on `C` by declaring a pr
esieve on `D`
to be covering if its image under `F` is.
-/
def comap (F : C ⥤ D) (J : Precoverage D) : Precoverage C where
  coverings Y := {R | R.map F ∈ J (F.obj Y)}

@[simp]
/-
**CategoryTheory.Precoverage.mem_comap_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Precoverage`。
形式化陈述：mem_comap_iff {X : C} {R : Presieve X} : R in J.comap F X ↔ R.map F in J (
F.obj X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_comap_iff {X : C} {R : Presieve X} :
    R ∈ J.comap F X ↔ R.map F ∈ J (F.obj X) := Iff.rfl
/-
**CategoryTheory.Precoverage.comap_inf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Precoverage`。
形式化陈述：comap_inf : (J ⊓ K).comap F = J.comap F ⊓ K.comap F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_inf : (J ⊓ K).comap F = J.comap F ⊓ K.comap F := rfl

@[simp]
/-
**CategoryTheory.Precoverage.comap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Precoverage`。
形式化陈述：comap_id (K : Precoverage C) : K.comap (𝟭 C) = K
参数：K : Precoverage C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ext`：∀ {C : Type u_1} {inst : CategoryTheory.
Category.{v_1, u_1} C} {x y : CategoryTheory.Precoverage C},   x.coverings = y.c
overings → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.map_id`：map_id {X : C} (R : Presieve X) : R.map 
(𝟭 C) = R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_id (K : Precoverage C) : K.comap (𝟭 C) = K := by
  ext
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Precoverage.comap_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Precoverage`。
形式化陈述：comap_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) (J : Precover
age E) : J.comap (F ⋙ G) = (J.comap G).comap F
参数：F : C ⥤ D；G : D ⥤ E；J : Precoverage E。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma comap_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) (J : Precoverage E) :
    J.comap (F ⋙ G) = (J.comap G).comap F := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

@[mono, gcongr]
/-
**CategoryTheory.Precoverage.comap_monotone** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Precoverage`。
形式化陈述：comap_monotone : Monotone (comap F)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_monotone : Monotone (comap F) :=
  fun _ _ hJK _ _ hR ↦ hJK _ hR
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasIsos J] : HasIsos (J.comap F) where
  mem_coverings_of_isIso {S T} f hf := by simpa using mem_coverings_of_isIso (F.map f)
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStableUnderComposition J] :
    IsStableUnderComposition (J.comap F) where
  comp_mem_coverings {ι} S Y f hf σ Z g hg := by
    simp only [mem_comap_iff, Presieve.map_ofArrows, Functor.map_comp] at hf hg ⊢
    exact J.comp_mem_coverings _ hf _ hg
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimitsOfShape WalkingCospan F] [IsStableUnderBaseChange J] :
    IsStableUnderBaseChange (J.comap F) where
  mem_coverings_of_isPullback {ι} S Y f hf Z g P p₁ p₂ h := by
    simp only [mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    exact mem_coverings_of_isPullback _ hf _ _ _
      fun i ↦ CategoryTheory.Functor.map_isPullback F (h i)
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CreatesLimitsOfShape WalkingCospan F] [HasPullbacks J] : HasPullbacks (J.comap F) where
  hasPullbacks_of_mem {X Y} R f hR := by
    refine ⟨fun {Z g} hg ↦ ?_⟩
    have : (Presieve.map F R).HasPullbacks (F.map f) := J.hasPullbacks_of_mem (F.map f) hR
    have : HasPullback (F.map g) (F.map f) := (R.map F).hasPullback _ (R.map_map hg)
    exact .of_createsLimit F g f

end Functoriality

end Precoverage

section PreservesPullbacks

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

open Limits

/-- A functor `F` preserves pairwise pullbacks of a presieve `R` if for every pair
of morphisms `f` and `g` in `R`, the pullback of `f` and `g` is preserved by `F`. -/
/-
**CategoryTheory.Functor.PreservesPairwisePullbacks** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D → {X : C} → CategoryTheory.Presieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves pairwise pullbacks of a presieve `R` if for every pair
of morphisms `f` and `g` in `R`, the pullback of `f` and `g` is preserved by `F`
.
-/
class Functor.PreservesPairwisePullbacks (F : C ⥤ D) {X : C} (R : Presieve X) : Prop where
  preservesLimit (R) ⦃Y Z : C⦄ ⦃f : Y ⟶ X⦄ ⦃g : Z ⟶ X⦄ : R f → R g →
    PreservesLimit (cospan f g) F := by infer_instance

alias Functor.preservesLimit_cospan_of_mem_presieve :=
  Functor.PreservesPairwisePullbacks.preservesLimit
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimitsOfShape WalkingCospan F] {X : C} (R : Presieve X) :
    F.PreservesPairwisePullbacks R where
/-
**CategoryTheory.Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.HasPairwisePullbacks`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) {X : C}   (R : CategoryTheory.Presieve X) [F.PreservesPairwisePullbacks R
] [R.HasPairwisePullbacks],   (CategoryTheory.Presieve.map F R).HasPairwisePullb
acks
参数：F : CategoryTheory.Functor C D；R : CategoryTheory.Presieve X；CategoryTheory.P
resieve.map F R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.HasPairwisePullbacks.has_pullbacks`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Pres
ieve X}   [self : R.HasPairwisePullbacks] {Y Z :…
· 使用定理 `CategoryTheory.Functor.preservesLimit_cospan_of_mem_presieve`：∀ {C : Typ
e u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : 
CategoryTheory.Category.{v_2, u_2} D} {F : Categor…
· 使用定理 `CategoryTheory.Limits.hasPullback_of_preservesPullback`：hasPullback_of_p
reservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g)
-/
lemma Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks {X : C} (R : Presieve X)
    [F.PreservesPairwisePullbacks R] [R.HasPairwisePullbacks] :
    (R.map F).HasPairwisePullbacks where
  has_pullbacks {Y Z} := fun {f} ⟨hf⟩ g ⟨hg⟩ ↦ by
    have := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    have := F.preservesLimit_cospan_of_mem_presieve _ hf hg
    exact hasPullback_of_preservesPullback F _ _

namespace Precoverage

/-- Pullbacks are preserved by a functor `F : C ⥤ D` for the precoverage `J` on `C` if
`F` preserves all pairwise pullbacks of presieves in `J`. -/
/-
**CategoryTheory.Precoverage.PullbacksPreservedBy** 是 Mathlib 中的一个类，位于命名空间 `Cate
goryTheory.Precoverage`。
形式化陈述：PullbacksPreservedBy (J : Precoverage C) (F : C ⥤ D) : Prop where preserve
sPairwisePullbacks_of_mem ⦃X : C⦄ ⦃R : Presieve X⦄ : R in J X -> F.PreservesPair
wisePullbacks R
参数：J : Precoverage C；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullbacks are preserved by a functor `F : C ⥤ D` for the precoverage `J` on `C` 
if
`F` preserves all pairwise pullbacks of presieves in `J`.
-/
class PullbacksPreservedBy (J : Precoverage C) (F : C ⥤ D) : Prop where
  preservesPairwisePullbacks_of_mem ⦃X : C⦄ ⦃R : Presieve X⦄ :
    R ∈ J X → F.PreservesPairwisePullbacks R := by infer_instance

alias preservesPairwisePullbacks_of_mem :=
  Precoverage.PullbacksPreservedBy.preservesPairwisePullbacks_of_mem
/-
**CategoryTheory.Precoverage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Precover
age`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Precoverage C) (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F] :
    J.PullbacksPreservedBy F where

end Precoverage

end PreservesPullbacks

end CategoryTheory

