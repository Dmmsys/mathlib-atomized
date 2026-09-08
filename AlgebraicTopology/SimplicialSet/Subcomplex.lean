/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Subfunctor.OfSection

/-!
# Subcomplexes of a simplicial set

Given a simplicial set `X`, this file defines the type `X.Subcomplex`
of subcomplexes of `X` as an abbreviation for `Subfunctor X`.
It also introduces a coercion from `X.Subcomplex` to `SSet`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits

namespace SSet

-- Note: this could be obtained as `inferInstanceAs (Balanced (_ ⥤ _))`
-- by importing `Mathlib.CategoryTheory.Adhesive.Basic`, but we give a
-- different proof so as to reduce imports
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Balanced SSet.{u} where
  isIso_of_mono_of_epi f _ _ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro
    rw [isIso_iff_bijective]
    constructor
    · rw [← mono_iff_injective]
      infer_instance
    · rw [← epi_iff_surjective]
      infer_instance

variable (X Y : SSet.{u})

/-- The complete lattice of subcomplexes of a simplicial set. -/
/-
**SSet.Subcomplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：Subcomplex
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete lattice of subcomplexes of a simplicial set.
-/
abbrev Subcomplex := Subfunctor X

variable {X Y}

namespace Subcomplex

/-- The underlying simplicial set of a subcomplex. -/
/-
**SSet.Subcomplex.toSSet** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：toSSet (A : X.Subcomplex) : SSet.{u}
参数：A : X.Subcomplex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying simplicial set of a subcomplex.
-/
abbrev toSSet (A : X.Subcomplex) : SSet.{u} := A.toFunctor
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut X.Subcomplex SSet.{u} where
  coe := fun S ↦ S.toSSet
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : SSet.{u}} (n : SimplexCategoryᵒᵖ) (A : X.Subcomplex)
    [DecidableEq (X.obj n)] :
    DecidableEq ((A : SSet).obj n) :=
  inferInstanceAs (DecidableEq (A.obj n))

/-- If `A : Subcomplex X`, this is the inclusion `A ⟶ X` in the category `SSet`. -/
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A : Subcomplex X`, this is the inclusion `A ⟶ X` in the category `SSet`.
-/
abbrev ι (A : Subcomplex X) : Quiver.Hom (V := SSet) A X := Subfunctor.ι A
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : X.Subcomplex) : Mono A.ι :=
  inferInstanceAs (Mono (Subfunctor.ι A))

section

variable {S₁ S₂ : X.Subcomplex} (h : S₁ ≤ S₂)

/-- Given an inequality `S₁ ≤ S₂` between subcomplexes of a simplicial set,
this is the induced morphism in the category `SSet`. -/
/-
**SSet.Subcomplex.homOfLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：homOfLE : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an inequality `S₁ ≤ S₂` between subcomplexes of a simplicial set,
this is the induced morphism in the category `SSet`.
-/
abbrev homOfLE : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u}) := Subfunctor.homOfLe h

@[reassoc]
/-
**SSet.Subcomplex.homOfLE_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：homOfLE_comp {S₃ : X.Subcomplex} (h' : S₂ <= S₃) : homOfLE h ≫ homOfLE h' 
= homOfLE (h.trans h')
参数：h' : S₂ <= S₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_comp {S₃ : X.Subcomplex} (h' : S₂ ≤ S₃) :
    homOfLE h ≫ homOfLE h' = homOfLE (h.trans h') := rfl

variable (S₁) in
@[simp]
/-
**SSet.Subcomplex.homOfLE_refl** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：homOfLE_refl : homOfLE (by rfl : S₁ <= S₁) = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_refl : homOfLE (by rfl : S₁ ≤ S₁) = 𝟙 _ := rfl

@[simp]
/-
**SSet.Subcomplex.homOfLE_app_val** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：homOfLE_app_val (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ) : dsimp% ((homOfLE 
h).app Δ x).val = x.val
参数：Δ : SimplexCategoryᵒᵖ；x : S₁.obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_app_val (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ) :
    dsimp% ((homOfLE h).app Δ x).val = x.val := rfl

@[simp, reassoc]
/-
**SSet.Subcomplex.homOfLE_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_ι : homOfLE h ≫ S₂.ι = S₁.ι := rfl
/-
**SSet.Subcomplex.mono_homOfLE** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
形式化陈述：mono_homOfLE : Mono (homOfLE h)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用引理 `SSet.Subcomplex.homOfLE_ι`：homOfLE_ι : homOfLE h ≫ S₂.ι = S₁.ι
-/
instance mono_homOfLE : Mono (homOfLE h) := mono_of_mono_fac (homOfLE_ι h)

/-- This is the isomorphism of simplicial sets corresponding to
an equality of subcomplexes. -/
@[simps]
/-
**SSet.Subcomplex.eqToIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：{X : _root_.SSet} → {S₁ S₂ : X.Subcomplex} → S₁ = S₂ → (S₁.toSSet ≅ S₂.toS
Set)
参数：S₁.toSSet ≅ S₂.toSSet。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the isomorphism of simplicial sets corresponding to
an equality of subcomplexes.
-/
protected def eqToIso (h : S₁ = S₂) : (S₁ : SSet.{u}) ≅ S₂ where
  hom := homOfLE h.le
  inv := homOfLE h.symm.le

end

/-- The functor which sends `A : X.Subcomplex` to `A.toSSet`. -/
@[simps]
/-
**SSet.Subcomplex.toSSetFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：toSSetFunctor : X.Subcomplex ⥤ SSet.{u} where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends `A : X.Subcomplex` to `A.toSSet`.
-/
def toSSetFunctor : X.Subcomplex ⥤ SSet.{u} where
  obj A := A
  map h := homOfLE (leOfHom h)

section

variable (X)

/-- If `X : SSet`, this is the isomorphism of simplicial sets
from `⊤ : X.Subcomplex` to `X`. -/
@[simps! inv_app_hom_apply]
/-
**SSet.Subcomplex.topIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：topIso : ((⊤ : X.Subcomplex) : SSet) ≅ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : SSet`, this is the isomorphism of simplicial sets
from `⊤ : X.Subcomplex` to `X`.
-/
def topIso : ((⊤ : X.Subcomplex) : SSet) ≅ X :=
  NatIso.ofComponents (fun n ↦ (Equiv.Set.univ (X.obj n)).toIso)

@[simp]
/-
**SSet.Subcomplex.topIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：topIso_hom : (topIso X).hom = Subcomplex.ι _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma topIso_hom : (topIso X).hom = Subcomplex.ι _ := rfl

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.topIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma topIso_inv_ι : (topIso X).inv ≫ Subfunctor.ι _ = 𝟙 _ := rfl

end

/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y) where
  allEq _ _ := by ext _ ⟨_, h⟩; tauto
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y) where
  default :=
    { app _ := ↾fun ⟨_, h⟩ ↦ by tauto
      naturality _ _ _ := by ext ⟨_, h⟩; tauto }
  uniq := by subsingleton

/-- If `X` is a simplicial set, then the empty subcomplex of `X` is an initial
object in `SSet`. -/
/-
**SSet.Subcomplex.isInitialBot** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：isInitialBot : IsInitial ((⊥ : X.Subcomplex) : SSet.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a simplicial set, then the empty subcomplex of `X` is an initial
object in `SSet`.
-/
def isInitialBot : IsInitial ((⊥ : X.Subcomplex) : SSet.{u}) :=
  IsInitial.ofUnique _

/-- The subcomplex of a simplicial set that is generated by a simplex. -/
/-
**SSet.Subcomplex.ofSimplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：ofSimplex {n : Nat} (x : X _⦋n⦌) : X.Subcomplex
参数：x : X _⦋n⦌。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subcomplex of a simplicial set that is generated by a simplex.
-/
abbrev ofSimplex {n : ℕ} (x : X _⦋n⦌) : X.Subcomplex := Subfunctor.ofSection x

@[simp]
/-
**SSet.Subcomplex.ofSimplex_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofSimplex_ι (x : X _⦋0⦌) : (ofSimplex x).ι = SSet.const x := by
  ext n ⟨_, ⟨u⟩, rfl⟩
  obtain rfl := Subsingleton.elim u (SimplexCategory.const _ _ 0)
  rfl
/-
**SSet.Subcomplex.mem_ofSimplex_obj** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：mem_ofSimplex_obj {n : Nat} (x : X _⦋n⦌) : x in (ofSimplex x).obj _
参数：x : X _⦋n⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subfunctor.mem_ofSection_obj`：mem_ofSection_obj : x in (o
fSection x).obj X
-/
lemma mem_ofSimplex_obj {n : ℕ} (x : X _⦋n⦌) :
    x ∈ (ofSimplex x).obj _ :=
  Subfunctor.mem_ofSection_obj x
/-
**SSet.Subcomplex.ofSimplex_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌) (A : X.Subcomplex) : ofSimplex x <
= A ↔ x in A.obj _
参数：x : X _⦋n⦌；A : X.Subcomplex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subfunctor.ofSection_le_iff`：ofSection_le_iff (G : Subfun
ctor F) : ofSection x <= G ↔ x in G.obj X
-/
lemma ofSimplex_le_iff {n : ℕ} (x : X _⦋n⦌) (A : X.Subcomplex) :
    ofSimplex x ≤ A ↔ x ∈ A.obj _ :=
  Subfunctor.ofSection_le_iff _ _
/-
**SSet.Subcomplex.mem_ofSimplex_obj_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：mem_ofSimplex_obj_iff {n : Nat} (x : X _⦋n⦌) {m : SimplexCategoryᵒᵖ} (y : 
X.obj m) : y in (ofSimplex x).obj m ↔ exists (f : m.unop ⟶ ⦋n⦌), X.map f.op x = 
y
参数：x : X _⦋n⦌；y : X.obj m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma mem_ofSimplex_obj_iff {n : ℕ} (x : X _⦋n⦌) {m : SimplexCategoryᵒᵖ} (y : X.obj m) :
    y ∈ (ofSimplex x).obj m ↔ ∃ (f : m.unop ⟶ ⦋n⦌), X.map f.op x = y := by
  dsimp [ofSimplex, Subfunctor.ofSection]
  aesop
/-
**SSet.Subcomplex.ofSimplex_map_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：ofSimplex_map_le {X : SSet.{u}} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) (x : X _⦋m⦌) :
 ofSimplex (X.map f.op x) <= ofSimplex x
参数：f : ⦋n⦌ ⟶ ⦋m⦌；x : X _⦋m⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofSimplex_map_le {X : SSet.{u}} {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) ≤ ofSimplex x := by
  simp only [Subfunctor.ofSection_le_iff]
  exact ⟨f.op, by simp⟩

@[simp]
/-
**SSet.Subcomplex.ofSimplex_map_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomple
x`。
形式化陈述：ofSimplex_map_of_epi {X : SSet.{u}} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] (x
 : X _⦋m⦌) : ofSimplex (X.map f.op x) = ofSimplex x
参数：f : ⦋n⦌ ⟶ ⦋m⦌；x : X _⦋m⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SSet.Subcomplex.ofSimplex_map_le`：ofSimplex_map_le {X : SSet.{u}} {n m :
 Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) (x : X _⦋m⦌) : ofSimplex (X.map f.op x) <= ofSimplex x
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofSimplex_map_of_epi {X : SSet.{u}} {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) = ofSimplex x := by
  refine le_antisymm (ofSimplex_map_le f x) ?_
  simp only [Subfunctor.ofSection_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← Functor.map_comp_apply, ← op_comp]⟩

section

variable (f : X ⟶ Y)

/-- The range of a morphism of simplicial sets, as a subcomplex. -/
/-
**SSet.Subcomplex.range** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：range : Y.Subcomplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of simplicial sets, as a subcomplex.
-/
abbrev range : Y.Subcomplex := Subfunctor.range f

/-- The morphism `X ⟶ Subcomplex.range f` induced by `f : X ⟶ Y`. -/
/-
**SSet.Subcomplex.toRange** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：toRange : X ⟶ Subcomplex.range f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X ⟶ Subcomplex.range f` induced by `f : X ⟶ Y`.
-/
abbrev toRange : X ⟶ Subcomplex.range f := Subfunctor.toRange f

@[simp, reassoc]
/-
**SSet.Subcomplex.toRange_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toRange_ι : toRange f ≫ (Subcomplex.range f).ι = f := rfl

@[simp]
/-
**SSet.Subcomplex.toRange_app_val** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：toRange_app_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) : dsimp% ((toRange f
).app Δ x).val = f.app Δ x
参数：x : X.obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toRange_app_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    dsimp% ((toRange f).app Δ x).val = f.app Δ x := rfl
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (toRange f) :=
  inferInstanceAs (Epi (Subfunctor.toRange f))
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : Mono (toRange f) :=
  mono_of_mono_fac (toRange_ι f)
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : IsIso (toRange f) :=
  isIso_of_mono_of_epi _
/-
**SSet.Subcomplex.range_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：range_eq_top_iff : Subcomplex.range f = ⊤ ↔ Epi f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.epi_iff_epi_app`：∀ {K : Type u} [inst : Category
Theory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} C]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Subfunctor.ext_iff`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryThe
ory.Subfunctor F}, x = …
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_eq_top_iff : Subcomplex.range f = ⊤ ↔ Epi f := by
  rw [NatTrans.epi_iff_epi_app, Subfunctor.ext_iff, funext_iff]
  simp only [epi_iff_surjective, Subfunctor.range_obj, Subfunctor.top_obj,
    Set.top_eq_univ, Set.range_eq_univ]
/-
**SSet.Subcomplex.range_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：range_eq_top [Epi f] : Subcomplex.range f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.range_eq_top_iff`：range_eq_top_iff : Subcomplex.range f 
= ⊤ ↔ Epi f
-/
lemma range_eq_top [Epi f] : Subcomplex.range f = ⊤ := by
  rwa [range_eq_top_iff]

end

section

variable (f : X ⟶ Y) {B : Y.Subcomplex} (hf : range f ≤ B)

/-- Given a morphism of simplicial sets `f : X ⟶ Y` whose
range is `≤ B` for some `B : Y.Subcomplex`, this is the
induced morphism `X ⟶ B`. -/
/-
**SSet.Subcomplex.lift** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：lift : X ⟶ B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of simplicial sets `f : X ⟶ Y` whose
range is `≤ B` for some `B : Y.Subcomplex`, this is the
induced morphism `X ⟶ B`.
-/
def lift : X ⟶ B := Subfunctor.lift f hf

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.lift_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_ι : lift f hf ≫ B.ι = f := rfl

@[simp]
/-
**SSet.Subcomplex.lift_app_coe** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：lift_app_coe {n : SimplexCategoryᵒᵖ} (x : X.obj n) : dsimp% ((lift f hf).a
pp _ x).1 = f.app _ x
参数：x : X.obj n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_app_coe {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    dsimp% ((lift f hf).app _ x).1 = f.app _ x := rfl

end

section

/-- The preimage of a subcomplex by a morphism of simplicial sets. -/
@[simps]
/-
**SSet.Subcomplex.preimage** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage (A : X.Subcomplex) (p : Y ⟶ X) : Y.Subcomplex where obj n
参数：A : X.Subcomplex；p : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a subcomplex by a morphism of simplicial sets.
-/
def preimage (A : X.Subcomplex) (p : Y ⟶ X) : Y.Subcomplex where
  obj n := p.app n ⁻¹' (A.obj n)
  map f := (Set.preimage_mono (A.map f)).trans (by simp [Set.preimage_preimage])

@[simp]
/-
**SSet.Subcomplex.preimage_max** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_max (A B : X.Subcomplex) (p : Y ⟶ X) : (A ⊔ B).preimage p = A.pre
image p ⊔ B.preimage p
参数：A B : X.Subcomplex；p : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_max (A B : X.Subcomplex) (p : Y ⟶ X) :
    (A ⊔ B).preimage p = A.preimage p ⊔ B.preimage p := rfl

@[simp]
/-
**SSet.Subcomplex.preimage_min** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_min (A B : X.Subcomplex) (p : Y ⟶ X) : (A ⊓ B).preimage p = A.pre
image p ⊓ B.preimage p
参数：A B : X.Subcomplex；p : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_min (A B : X.Subcomplex) (p : Y ⟶ X) :
    (A ⊓ B).preimage p = A.preimage p ⊓ B.preimage p := rfl

@[simp]
/-
**SSet.Subcomplex.preimage_iSup** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_iSup {ι : Type*} (A : ι -> X.Subcomplex) (p : Y ⟶ X) : (⨆ i, A i)
.preimage p = ⨆ i, (A i).preimage p
参数：A : ι -> X.Subcomplex；p : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_iSup {ι : Type*} (A : ι → X.Subcomplex) (p : Y ⟶ X) :
    (⨆ i, A i).preimage p = ⨆ i, (A i).preimage p := by aesop

@[simp]
/-
**SSet.Subcomplex.preimage_iInf** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_iInf {ι : Type*} (A : ι -> X.Subcomplex) (p : Y ⟶ X) : (⨅ i, A i)
.preimage p = ⨅ i, (A i).preimage p
参数：A : ι -> X.Subcomplex；p : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用引理 `CategoryTheory.Subfunctor.iInf_obj`：iInf_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨅ i, S i).obj U = ⋂ i, (S i).obj U
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_iInf {ι : Type*} (A : ι → X.Subcomplex) (p : Y ⟶ X) :
    (⨅ i, A i).preimage p = ⨅ i, (A i).preimage p := by aesop

@[simp]
/-
**SSet.Subcomplex.preimage_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_id (A : X.Subcomplex) : A.preimage (𝟙 X) = A
参数：A : X.Subcomplex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_id (A : X.Subcomplex) : A.preimage (𝟙 X) = A := rfl
/-
**SSet.Subcomplex.preimage_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_comp {Z : SSet.{u}} (A : Z.Subcomplex) (f : X ⟶ Y) (g : Y ⟶ Z) : 
A.preimage (f ≫ g) = (A.preimage g).preimage f
参数：A : Z.Subcomplex；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_comp {Z : SSet.{u}} (A : Z.Subcomplex) (f : X ⟶ Y) (g : Y ⟶ Z) :
    A.preimage (f ≫ g) = (A.preimage g).preimage f := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SSet.Subcomplex.preimage_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_ι (A : X.Subcomplex) : A.preimage A.ι = ⊤ := by aesop

end

section

variable (A : X.Subcomplex) (f : X ⟶ Y)

/-- The image of a subcomplex by a morphism of simplicial sets. -/
@[simps!]
/-
**SSet.Subcomplex.image** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image : Y.Subcomplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a subcomplex by a morphism of simplicial sets.
-/
def image : Y.Subcomplex := Subfunctor.image A f
/-
**SSet.Subcomplex.image_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_le_iff (Z : Y.Subcomplex) : A.image f <= Z ↔ A <= Z.preimage f
参数：Z : Y.Subcomplex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_le_iff (Z : Y.Subcomplex) :
    A.image f ≤ Z ↔ A ≤ Z.preimage f := by
  simp [Subfunctor.le_def]
/-
**SSet.Subcomplex.image_top** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_top : (⊤ : X.Subcomplex).image f = range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_top : (⊤ : X.Subcomplex).image f = range f := by aesop

@[simp]
/-
**SSet.Subcomplex.image_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_id : A.image (𝟙 _) = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_id : A.image (𝟙 _) = A := by aesop
/-
**SSet.Subcomplex.image_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_comp {Z : SSet.{u}} (g : Y ⟶ Z) : A.image (f ≫ g) = (A.image f).imag
e g
参数：g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_comp {Z : SSet.{u}} (g : Y ⟶ Z) :
    A.image (f ≫ g) = (A.image f).image g := by aesop
/-
**SSet.Subcomplex.range_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：range_comp {Z : SSet.{u}} (g : Y ⟶ Z) : Subcomplex.range (f ≫ g) = (Subcom
plex.range f).image g
参数：g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_comp {Z : SSet.{u}} (g : Y ⟶ Z) :
    Subcomplex.range (f ≫ g) = (Subcomplex.range f).image g := by aesop

set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.image_eq_range** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_eq_range : A.image f = range (A.ι ≫ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma image_eq_range : A.image f = range (A.ι ≫ f) := by aesop
/-
**SSet.Subcomplex.image_iSup** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_iSup {ι : Type*} (S : ι -> X.Subcomplex) (f : X ⟶ Y) : image (⨆ i, S
 i) f = ⨆ i, (S i).image f
参数：S : ι -> X.Subcomplex；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
-/
lemma image_iSup {ι : Type*} (S : ι → X.Subcomplex) (f : X ⟶ Y) :
    image (⨆ i, S i) f = ⨆ i, (S i).image f := by
  aesop

@[simp]
/-
**SSet.Subcomplex.preimage_range** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_range : (range f).preimage f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.image_le_iff`：image_le_iff (Z : Y.Subcomplex) : A.image 
f <= Z ↔ A <= Z.preimage f
· 使用引理 `SSet.Subcomplex.image_top`：image_top : (⊤ : X.Subcomplex).image f = rang
e f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma preimage_range : (range f).preimage f = ⊤ :=
  le_antisymm (by simp) (by rw [← image_le_iff, image_top])

@[simp]
/-
**SSet.Subcomplex.image_le_range** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_le_range : A.image f <= range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.preimage_range`：preimage_range : (range f).preimage f = 
⊤
-/
lemma image_le_range : A.image f ≤ range f := by
  simp [image_le_iff, preimage_range, le_top]

@[simp]
/-
**SSet.Subcomplex.image_ofSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_ofSimplex {n : Nat} (x : X _⦋n⦌) (f : X ⟶ Y) : (ofSimplex x).image f
 = ofSimplex (f.app _ x)
参数：x : X _⦋n⦌；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.image_le_iff`：image_le_iff (Z : Y.Subcomplex) : A.image 
f <= Z ↔ A <= Z.preimage f
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用引理 `SSet.Subcomplex.mem_ofSimplex_obj`：mem_ofSimplex_obj {n : Nat} (x : X _⦋
n⦌) : x in (ofSimplex x).obj _
-/
lemma image_ofSimplex {n : ℕ} (x : X _⦋n⦌) (f : X ⟶ Y) :
    (ofSimplex x).image f = ofSimplex (f.app _ x) := by
  apply le_antisymm
  · rw [image_le_iff, ofSimplex_le_iff, preimage_obj, Set.mem_preimage]
    apply mem_ofSimplex_obj
  · rw [ofSimplex_le_iff]
    exact ⟨x, mem_ofSimplex_obj _, rfl⟩

/-- Given a morphism of simplicial sets `f : X ⟶ Y` and a subcomplex `A` of `X`,
this is the induced morphism from `A` to `A.image f`. -/
@[simps! +dsimpLhs]
/-
**SSet.Subcomplex.toImage** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：toImage : (A : SSet) ⟶ (A.image f : SSet)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of simplicial sets `f : X ⟶ Y` and a subcomplex `A` of `X`,
this is the induced morphism from `A` to `A.image f`.
-/
def toImage : (A : SSet) ⟶ (A.image f : SSet) :=
  (A.image f).lift (A.ι ≫ f) (by rw [image_eq_range])

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.toImage_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toImage_ι : A.toImage f ≫ (A.image f).ι = A.ι ≫ f := rfl
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (A.toImage f) := by
  rw [← range_eq_top_iff]
  apply le_antisymm (by simp)
  rintro m ⟨_, ⟨y, hy, rfl⟩⟩ _
  exact ⟨⟨y, hy⟩, rfl⟩
/-
**SSet.Subcomplex.image_monotone** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_monotone : Monotone (fun (S : X.Subcomplex) => S.image f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.image_le_iff`：image_le_iff (Z : Y.Subcomplex) : A.image 
f <= Z ↔ A <= Z.preimage f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma image_monotone : Monotone (fun (S : X.Subcomplex) ↦ S.image f) := by
  intro S T h
  rw [image_le_iff]
  exact h.trans (by rw [← image_le_iff])

end

/-
**SSet.Subcomplex.preimage_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex
`。
形式化陈述：preimage_eq_top_iff (B : X.Subcomplex) (f : Y ⟶ X) : B.preimage f = ⊤ ↔ ra
nge f <= B
参数：B : X.Subcomplex；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.image_top`：image_top : (⊤ : X.Subcomplex).image f = rang
e f
· 使用引理 `SSet.Subcomplex.image_le_iff`：image_le_iff (Z : Y.Subcomplex) : A.image 
f <= Z ↔ A <= Z.preimage f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preimage_eq_top_iff (B : X.Subcomplex) (f : Y ⟶ X) :
    B.preimage f = ⊤ ↔ range f ≤ B := by
  rw [← image_top, image_le_iff, top_le_iff]

@[simp]
/-
**SSet.Subcomplex.image_preimage_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_preimage_le (B : X.Subcomplex) (f : Y ⟶ X) : (B.preimage f).image f 
<= B
参数：B : X.Subcomplex；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.image_le_iff`：image_le_iff (Z : Y.Subcomplex) : A.image 
f <= Z ↔ A <= Z.preimage f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma image_preimage_le (B : X.Subcomplex) (f : Y ⟶ X) :
    (B.preimage f).image f ≤ B := by
  rw [image_le_iff]

@[simp]
/-
**SSet.Subcomplex.preimage_image_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcom
plex`。
形式化陈述：preimage_image_of_isIso (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f] : (B.prei
mage f).image f = B
参数：f : X ⟶ Y；B : Y.Subcomplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SSet.Subcomplex.image_preimage_le`：image_preimage_le (B : X.Subcomplex) 
(f : Y ⟶ X) : (B.preimage f).image f <= B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma preimage_image_of_isIso (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f] :
    (B.preimage f).image f = B := by
  apply le_antisymm (B.image_preimage_le f)
  · intro n y hy
    exact ⟨(inv f).app _ y, by simpa [← NatIso.isIso_inv_app, ← NatTrans.comp_app_apply]⟩
/-
**SSet.Subcomplex.preimage_inv** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：preimage_inv {X Y : SSet.{u}} (A : Subcomplex X) (f : X ⟶ Y) [IsIso f] : A
.preimage (inv f) = A.image f
参数：A : Subcomplex X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `SSet.Subcomplex.image_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (f :
 X ⟶ Y) (i : SimplexCategoryᵒᵖ),   (A.image f).obj i = ⇑(CategoryTheory.Concrete
Category.hom (f…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f]   {F 
: C → C → Type uF} {carrier…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f]   {F 
: C → C → Type uF} {carrier…
-/
lemma preimage_inv {X Y : SSet.{u}} (A : Subcomplex X) (f : X ⟶ Y) [IsIso f] :
    A.preimage (inv f) = A.image f := by
  ext _ x
  simp only [preimage_obj, NatIso.isIso_inv_app, Set.mem_preimage, image_obj, Set.mem_image]
  exact ⟨fun hx ↦ ⟨(inv f).app _ x, by simpa⟩, by rintro ⟨x, hx, rfl⟩; simpa⟩
/-
**SSet.Subcomplex.image_inv** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：image_inv {X Y : SSet.{u}} (A : Subcomplex Y) (f : X ⟶ Y) [IsIso f] : A.im
age (inv f) = A.preimage f
参数：A : Subcomplex Y；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_inv`：inv_inv [IsIso f] : inv (inv f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_inv {X Y : SSet.{u}} (A : Subcomplex Y) (f : X ⟶ Y) [IsIso f] :
    A.image (inv f) = A.preimage f := by
  simp [← preimage_inv]

/-- Given a morphism of simplicial sets `p : Y ⟶ X` and
`A : X.Subcomplex`, this is the induced morphism
`(A.preimage p : SSet) ⟶ (A : SSet)`. -/
@[simps! +dsimpLhs]
/-
**SSet.Subcomplex.fromPreimage** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：fromPreimage (A : X.Subcomplex) (p : Y ⟶ X) : (A.preimage p : SSet) ⟶ (A :
 SSet)
参数：A : X.Subcomplex；p : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of simplicial sets `p : Y ⟶ X` and
`A : X.Subcomplex`, this is the induced morphism
`(A.preimage p : SSet) ⟶ (A : SSet)`.
-/
def fromPreimage (A : X.Subcomplex) (p : Y ⟶ X) :
    (A.preimage p : SSet) ⟶ (A : SSet) :=
  lift (Subcomplex.ι _ ≫ p) (by simp [range_comp])

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.fromPreimage_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromPreimage_ι (A : X.Subcomplex) (p : Y ⟶ X) :
    A.fromPreimage p ≫ A.ι = (A.preimage p).ι ≫ p := rfl

end Subcomplex

end SSet

