/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# The relative cell complex attached to a rank function for a pairing

Let `A` be a subcomplex of a simplicial set `X`. Let `P : A.Pairing`
be a proper pairing (in the sense of Moss) and `f : P.RankFunction ι`
be a rank function. We show that the inclusion `A.ι` is a relative
cell complex with basic cells given by horn inclusions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v u

open CategoryTheory HomotopicalAlgebra Simplicial Limits Opposite

namespace SSet.Subcomplex.Pairing.RankFunction

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing}
  {ι : Type v} [LinearOrder ι] (f : P.RankFunction ι)

/-- Given a rank function `f : P.RankFunction ι` for a
pairing `P` of a subcomplex `A` of `X : SSet`, and `i : ι`,
this is the type of type (II) simplices of rank `i`. -/
@[ext]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Su
bcomplex.Pairing.RankFunction`。
形式化陈述：{X : _root_.SSet} →   {A : X.Subcomplex} → {P : A.Pairing} → {ι : Type v} 
→ [inst : LinearOrder ι] → P.RankFunction ι → ι → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank function `f : P.RankFunction ι` for a
pairing `P` of a subcomplex `A` of `X : SSet`, and `i : ι`,
this is the type of type (II) simplices of rank `i`.
-/
structure Cell (i : ι) : Type u where
  /-- a type (II) simplex -/
  s : P.II
  rank_s : f.rank s = i

namespace Cell

variable {f} {i : ι} (c : f.Cell i)

/-- The dimension `c.dim` of a cell `c` of a rank function for a
pairing `P` of a subcomplex of a simplicial set. This is defined
as the dimension of the corresponding type (II) simplex.
(In the case `P` is proper, the corresponding type (I) simplex
will be of dimension `c.dim + 1`.) -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.dim** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSe
t.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：dim : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dimension `c.dim` of a cell `c` of a rank function for a
pairing `P` of a subcomplex of a simplicial set. This is defined
as the dimension of the corresponding type (II) simplex.
(In the case `P` is proper, the corresponding type (I) simplex
will be of dimension `c.dim + 1`.)
-/
abbrev dim : ℕ := c.s.val.dim

variable [P.IsProper]

/-- If `c` is a cell of a rank function for a proper pairing `P`
of a subcomplex of a simplicial set, this is the index
in `Fin (c.dim + 2)` of the face of the type (I) simplex
given by the corresponding type (II) simplex. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.index** 是 Mathlib 中的一个定义，位于命名空间 `SSe
t.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：index : Fin (c.dim + 2)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a cell of a rank function for a proper pairing `P`
of a subcomplex of a simplicial set, this is the index
in `Fin (c.dim + 2)` of the face of the type (I) simplex
given by the corresponding type (II) simplex.
-/
noncomputable def index : Fin (c.dim + 2) :=
  (P.isUniquelyCodimOneFace c.s).index rfl

/-- The horn in the standard simplex corresponding to a cell
of a rank function for a proper pairing of a subcomplex of
a simplicial set. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.horn** 是 Mathlib 中的一个定义，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：{X : _root_.SSet} →   {A : X.Subcomplex} →     {P : A.Pairing} →       {ι 
: Type v} →         [inst : LinearOrder ι] →           {f : P.RankFunction ι} → 
            {i : ι} → (c : f.Cell i) → [P.IsProper] → (SSet.stdSimplex.obj { len
 := c.dim + 1 }).Subcomplex
参数：c : f.Cell i；SSet.stdSimplex.obj { len := c.dim + 1 }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horn in the standard simplex corresponding to a cell
of a rank function for a proper pairing of a subcomplex of
a simplicial set.
-/
protected noncomputable abbrev horn : (Δ[c.dim + 1] : SSet.{u}).Subcomplex :=
  SSet.horn _ c.index

/-- The morphism `Δ[c.dim + 1] ⟶ X` corresponding to a cell of
a rank function for a proper pairing of a subcomplex of `X : SSet`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSe
t.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：map : Δ[c.dim + 1] ⟶ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The morphism `Δ[c.dim + 1] ⟶ X` corresponding to a cell of
a rank function for a proper pairing of a subcomplex of `X : SSet`.
-/
abbrev map : Δ[c.dim + 1] ⟶ X :=
  yonedaEquiv.symm
    ((P.p c.s).val.cast (P.isUniquelyCodimOneFace c.s).dim_eq).simplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.range_map** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：range_map : Subcomplex.range c.map = (P.p c.s).val.subcomplex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.range_eq_ofSimplex`：range_eq_ofSimplex {n : Nat} (f : Δ[
n] ⟶ X) : range f = ofSimplex (yonedaEquiv f)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `SSet.S.ofSimplex_eq_subcomplex_mk`：ofSimplex_eq_subcomplex_mk {n : Nat} 
(x : X _⦋n⦌) : Subcomplex.ofSimplex x = (S.mk x).subcomplex
· 使用引理 `SSet.Subcomplex.Pairing.dim_p`：dim_p [P.IsProper] (x : P.II) : (P.p x).1
.dim = x.1.dim + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.S.cast_eq_self`：cast_eq_self : s.cast hd = s
-/
lemma range_map : Subcomplex.range c.map = (P.p c.s).val.subcomplex := by
  rw [range_eq_ofSimplex, Equiv.apply_symm_apply, S.ofSimplex_eq_subcomplex_mk,
    ← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp [S.subcomplex]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.map_app_objEquiv_symm_** 是 Mathlib 中
的一个引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction.Cell`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_app_objEquiv_symm_δ_index :
    c.map.app (op ⦋c.dim⦌) (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index)) =
      c.s.val.simplex :=
  (P.isUniquelyCodimOneFace c.s).δ_index rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.subcomplex_not_le_image_horn** 是 Mat
hlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：subcomplex_not_le_image_horn : ¬ c.s.val.subcomplex <= c.horn.image c.map
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `SSet.mono_of_nonDegenerate`：mono_of_nonDegenerate (x : X.nonDegenerate n
) {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) (y : X.obj (op m)) (hy : X.map f.op y = x)
 : Mono f
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.stdSimplex.map_objEquiv_op_apply`：map_objEquiv_op_apply {X : SSet.{
u}} {n : SimplexCategory} (x : X.obj (op n)) {m : SimplexCategoryᵒᵖ} (y : (stdSi
mplex.obj n).obj m) : dsimp…
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
· 使用引理 `SSet.stdSimplex.face_singleton_compl`：face_singleton_compl {n : Nat} (i 
: Fin (n + 2)) : face.{u} {i}ᶜ = Subcomplex.ofSimplex (objEquiv.symm (SimplexCat
egory.δ i))
· 使用引理 `SSet.subcomplex_le_horn_iff`：subcomplex_le_horn_iff {n : Nat} (A : Δ[n +
 1].Subcomplex) (i : Fin (n + 2)) : A <= horn.{u} (n + 1) i ↔ ¬ stdSimplex.face 
{i}ᶜ <= A
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.unique`：unique (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f
] (hf : X.map f.op (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simpl
ex) : f = SimplexCategory.…
-/
lemma subcomplex_not_le_image_horn : ¬ c.s.val.subcomplex ≤ c.horn.image c.map := by
  intro h
  simp only [Subfunctor.ofSection_le_iff, image_obj, Set.mem_image] at h
  obtain ⟨x, h₁, h₂⟩ := h
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [← stdSimplex.map_objEquiv_op_apply, Equiv.apply_symm_apply] at h₂
  have := mono_of_nonDegenerate (x := ⟨_, c.s.val.nonDegenerate⟩) _ _ _ h₂
  obtain rfl := (P.isUniquelyCodimOneFace c.s).unique rfl _ h₂
  rw [← ofSimplex_le_iff, subcomplex_le_horn_iff, ← stdSimplex.face_singleton_compl] at h₁
  tauto
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.image_horn_lt_subcomplex** 是 Mathlib
 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：image_horn_lt_subcomplex : c.horn.image c.map < (P.p c.s).val.subcomplex
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.Cell.range_map`：range_map : Subcomp
lex.range c.map = (P.p c.s).val.subcomplex
· 使用引理 `SSet.Subcomplex.image_le_range`：image_le_range : A.image f <= range f
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.Cell.subcomplex_not_le_image_horn`：
subcomplex_not_le_image_horn : ¬ c.s.val.subcomplex <= c.horn.image c.map
· 使用引理 `SSet.Subcomplex.Pairing.le`：le [P.IsProper] (x : P.II) : x.1 <= (P.p x).
1
-/
lemma image_horn_lt_subcomplex : c.horn.image c.map < (P.p c.s).val.subcomplex := by
  rw [lt_iff_le_and_ne]
  exact ⟨by simpa using! image_le_range c.horn c.map,
    fun h ↦ c.subcomplex_not_le_image_horn (by simpa only [h] using! P.le c.s)⟩

@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.image_face_index_compl** 是 Mathlib 中
的一个引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：image_face_index_compl : (stdSimplex.face {c.index}ᶜ).image c.map = c.s.va
l.subcomplex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.face_singleton_compl`：face_singleton_compl {n : Nat} (i 
: Fin (n + 2)) : face.{u} {i}ᶜ = Subcomplex.ofSimplex (objEquiv.symm (SimplexCat
egory.δ i))
· 使用引理 `SSet.Subcomplex.image_ofSimplex`：image_ofSimplex {n : Nat} (x : X _⦋n⦌) 
(f : X ⟶ Y) : (ofSimplex x).image f = ofSimplex (f.app _ x)
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_index`：δ_index : X.δ (hxy.index hd) (y.c
ast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
-/
lemma image_face_index_compl :
    (stdSimplex.face {c.index}ᶜ).image c.map = c.s.val.subcomplex := by
  rw [stdSimplex.face_singleton_compl, image_ofSimplex]
  congr 1
  exact (P.isUniquelyCodimOneFace c.s).δ_index rfl

end Cell

variable [P.IsProper] in
/-- The horn inclusion corresponding to a cell of a rank function
for a proper pairing of a subcomplex of a simplicial set. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.basicCell** 是 Mathlib 中的一个缩写定义，位于命名空间 `SS
et.Subcomplex.Pairing.RankFunction`。
形式化陈述：basicCell (i : ι) (c : f.Cell i) : (c.horn : SSet) ⟶ Δ[c.dim + 1]
参数：i : ι；c : f.Cell i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horn inclusion corresponding to a cell of a rank function
for a proper pairing of a subcomplex of a simplicial set.
-/
noncomputable abbrev basicCell (i : ι) (c : f.Cell i) : (c.horn : SSet) ⟶ Δ[c.dim + 1] :=
  c.horn.ι

/-- The filtration of a simplicial set given by a rank function
for a proper pairing of a subcomplex. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.filtration** 是 Mathlib 中的一个定义，位于命名空间 `SSe
t.Subcomplex.Pairing.RankFunction`。
形式化陈述：filtration (i : ι) : X.Subcomplex
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filtration of a simplicial set given by a rank function
for a proper pairing of a subcomplex.
-/
def filtration (i : ι) : X.Subcomplex :=
  A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex
/-
**SSet.Subcomplex.Pairing.RankFunction.filtration_def** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：filtration_def (i : ι) : f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f
.Cell j), (P.p c.s).val.subcomplex
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma filtration_def (i : ι) :
    f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex :=
  rfl
/-
**SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration** 是 Mathlib 中的一个
引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：subcomplex_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p
 c.s).val.subcomplex <= f.filtration i
参数：c : f.Cell j；h : j < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma subcomplex_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) :
    (P.p c.s).val.subcomplex ≤ f.filtration i := by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.le_filtration** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：le_filtration (i : ι) : A <= f.filtration i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma le_filtration (i : ι) : A ≤ f.filtration i := le_sup_left

@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.filtration_bot** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：filtration_bot [OrderBot ι] : f.filtration ⊥ = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filtration_bot [OrderBot ι] : f.filtration ⊥ = A := by
  simp [filtration_def]
/-
**SSet.Subcomplex.Pairing.RankFunction.filtration_monotone** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：filtration_monotone : Monotone f.filtration
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_def`：filtration_def (i :
 ι) : f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.s
ubcomplex
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration`：subcomple
x_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p c.s).val.subco
mplex <= f.filtration i
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma filtration_monotone : Monotone f.filtration := by
  intro i₁ i₂ h
  conv_lhs => rw [filtration_def]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.subcomplex_le_filtration c (lt_of_lt_of_le hj h)
/-
**SSet.Subcomplex.Pairing.RankFunction.filtration_succ** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：filtration_succ [SuccOrder ι] (i : ι) (hi : ¬ IsMax i) : f.filtration (Ord
er.succ i) = f.filtration i ⊔ ⨆ (c : f.Cell i), (P.p c.s).val.subcomplex
参数：i : ι；hi : ¬ IsMax i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_def`：filtration_def (i :
 ι) : f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.s
ubcomplex
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.le_filtration`：le_filtration (i : ι
) : A <= f.filtration i
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration`：subcomple
x_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p c.s).val.subco
mplex <= f.filtration i
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
-/
lemma filtration_succ [SuccOrder ι] (i : ι) (hi : ¬ IsMax i) :
    f.filtration (Order.succ i) =
      f.filtration i ⊔ ⨆ (c : f.Cell i), (P.p c.s).val.subcomplex := by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c ↦ ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.subcomplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c ↦ f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩
/-
**SSet.Subcomplex.Pairing.RankFunction.filtration_of_isSuccLimit** 是 Mathlib 中的一
个引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι] (i : ι) (hi : Order.I
sSuccLimit i) : f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j
参数：i : ι；hi : Order.IsSuccLimit i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_def`：filtration_def (i :
 ι) : f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.s
ubcomplex
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_bot`：filtration_bot [Ord
erBot ι] : f.filtration ⊥ = A
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration`：subcomple
x_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p c.s).val.subco
mplex <= f.filtration i
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsSuccLimit.succ_lt_iff`：∀ {α : Type u_1} {a b : α} [inst : Partia
lOrder α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → (Order.succ a < b ↔ a 
< b)
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι] (i : ι) (hi : Order.IsSuccLimit i) :
    f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j := by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c ↦ ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le
/-
**SSet.Subcomplex.Pairing.RankFunction.iSup_filtration_iio** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：iSup_filtration_iio [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccL
imit m) : ⨆ (i : Set.Iio m), f.filtration i = f.filtration m
参数：m : ι；hm : Order.IsSuccLimit m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_def`：filtration_def (i :
 ι) : f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.s
ubcomplex
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_bot`：filtration_bot [Ord
erBot ι] : f.filtration ⊥ = A
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration`：subcomple
x_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p c.s).val.subco
mplex <= f.filtration i
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `not_isMax_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.IsSuccLimit.succ_lt_iff`：∀ {α : Type u_1} {a b : α} [inst : Partia
lOrder α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → (Order.succ a < b ↔ a 
< b)
-/
lemma iSup_filtration_iio [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccLimit m) :
    ⨆ (i : Set.Iio m), f.filtration i = f.filtration m := by
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c ↦
      (f.subcomplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.mpr hj⟩))⟩

variable {f} in
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.subcomplex_not_le_filtration** 是 Mat
hlib 中的一个定理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst 
: LinearOrder ι] {f : P.RankFunction ι}   {j : ι} (c : f.Cell j), ¬(↑c.s).subcom
plex ≤ f.filtration j
参数：c : f.Cell j；↑c.s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.rank_s`：∀ {X : _root_.SSet} {A
 : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f : P.Rank
Function ι}   {i : ι} (self : f.Cell i…
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.lt`：∀ {X : _root_.SSet} {A : X.Subc
omplex} {P : A.Pairing} {α : Type v} [inst : PartialOrder α] (self : P.RankFunct
ion α)   {x y : ↑P.II}, P.Anc…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `SSet.Subcomplex.N.le_iff`：le_iff {x y : A.N} : x <= y ↔ x.toN <= y.toN
· 使用引理 `SSet.N.le_iff`：le_iff {x y : X.N} : x <= y ↔ x.subcomplex <= y.subcomple
x
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `SSet.Subcomplex.Pairing.ne`：ne (x : P.I) (y : P.II) : x.1 != y.1
-/
lemma Cell.subcomplex_not_le_filtration {j : ι} (c : f.Cell j) :
    ¬ c.s.val.subcomplex ≤ f.filtration j := by
  simp only [ofSimplex_le_iff, filtration_def, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, not_or, not_exists]
  refine ⟨c.s.val.notMem, fun i hi c' h ↦ ?_⟩
  rw [← c.rank_s, ← c'.rank_s] at hi
  refine lt_irrefl _ (hi.trans (f.lt ?_))
  refine ⟨fun hxy ↦ ?_, lt_of_le_of_ne ?_ ((P.ne _ _).symm)⟩
  · rw [hxy] at hi
    exact (lt_irrefl _ hi).elim
  · rw [← ofSimplex_le_iff] at h
    rwa [Subcomplex.N.le_iff, SSet.N.le_iff]

variable [P.IsProper]
/-
**SSet.Subcomplex.Pairing.RankFunction.iSup_filtration** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：iSup_filtration [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι] : ⨆ (i : ι), f.f
iltration i = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.N.subcomplex_le_iff`：subcomplex_le_iff {A B : X.Subcomplex} : A <= 
B ↔ forall (s : X.N), s.subcomplex <= A -> s.subcomplex <= B
· 使用引理 `SSet.Subcomplex.N.cases`：cases {motive : X.N -> Prop} (mem : forall (s :
 X.N), s.subcomplex <= A -> motive s) (notMem : forall (s : A.N), motive s.toN) 
(s : X.N) : m…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_bot`：filtration_bot [Ord
erBot ι] : f.filtration ⊥ = A
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `SSet.Subcomplex.Pairing.exists_or`：exists_or (x : A.N) : exists (y : P.I
I), x = y ∨ x = P.p y
· 使用引理 `SSet.Subcomplex.Pairing.le`：le [P.IsProper] (x : P.II) : x.1 <= (P.p x).
1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration`：subcomple
x_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p c.s).val.subco
mplex <= f.filtration i
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
-/
lemma iSup_filtration [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι] :
    ⨆ (i : ι), f.filtration i = ⊤ := by
  refine le_antisymm (by simp) ?_
  rw [N.subcomplex_le_iff]
  intro s _
  cases s using SSet.Subcomplex.N.cases A with
  | mem s hs => exact hs.trans (le_trans (by simp) (le_iSup _ ⊥))
  | notMem s =>
    obtain ⟨t, ht⟩ := P.exists_or s
    refine le_trans ?_
      (le_trans (f.subcomplex_le_filtration ⟨t, rfl⟩ (Order.lt_succ _)) (le_iSup _ _))
    obtain rfl | rfl := ht
    · exact P.le t
    · rfl

variable {f} in
/-- The morphism `Δ[c.dim + 1] ⟶ f.filtration (Order.succ j)` given
by `c : f.Cell j`, when `f` is a rank function for a proper pairing
of a subcomplex of a simplicial set. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.mapToSucc** 是 Mathlib 中的一个定义，位于命名空间 
`SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：{X : _root_.SSet} →   {A : X.Subcomplex} →     {P : A.Pairing} →       {ι 
: Type v} →         [inst : LinearOrder ι] →           {f : P.RankFunction ι} → 
            [P.IsProper] →               {j : ι} →                 [inst_2 : Suc
cOrder ι] →                   [NoMaxOrder ι] →                     (c : f.Cell j
) → SSet.stdSimplex.obj { len := c.dim + 1 } ⟶ (f.filtration (Order.succ j)).toS
Set
参数：c : f.Cell j；f.filtration (Order.succ j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Δ[c.dim + 1] ⟶ f.filtration (Order.succ j)` given
by `c : f.Cell j`, when `f` is a rank function for a proper pairing
of a subcomplex of a simplicial set.
-/
def Cell.mapToSucc {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j) :
    Δ[c.dim + 1] ⟶ f.filtration (Order.succ j) :=
  Subcomplex.lift c.map (by simpa using f.subcomplex_le_filtration c (Order.lt_succ _))

variable {f} in
@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.mapToSucc_** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.mapToSucc_ι {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j) :
    c.mapToSucc ≫ (f.filtration (Order.succ j)).ι = c.map := rfl

section

/-!
The main technical result in this section is `SSet.Subcomplex.Pairing.RankFunction.isPushout`
which states that there is a pushout square:
```
                                      f.t j
∐ fun (c : f.Cell j) ↦ c.horn  -------------> f.filtration j
               |                                   |
         f.m j |                                   |
               v                      f.b j        v
∐ fun (c : f.Cell j) ↦ Δ[c.dim + 1]  -------> f.filtration (Order.succ j)
```
The map on the left is a coproduct of horn inclusions (the source and target
of the morphism `f.m j` are denoted `f.sigmaHorn j` and `f.sigmaStdSimplex j`).

-/

/-- Given a rank function for a proper pairing of a subcomplex of a
simplicial set, this is the coproduct of the horns corresponding to
all cells of rank `j`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.sigmaHorn** 是 Mathlib 中的一个缩写定义，位于命名空间 `SS
et.Subcomplex.Pairing.RankFunction`。
形式化陈述：sigmaHorn (j : ι) : SSet.{u}
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank function for a proper pairing of a subcomplex of a
simplicial set, this is the coproduct of the horns corresponding to
all cells of rank `j`.
-/
noncomputable abbrev sigmaHorn (j : ι) : SSet.{u} :=
  ∐ fun (c : f.Cell j) ↦ c.horn

variable {f} in
/-- Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the inclusion of
`c.horn` into `f.sigmaHorn j`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.S
ubcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the inclusion of
`c.horn` into `f.sigmaHorn j`.
-/
noncomputable abbrev Cell.ιSigmaHorn {j : ι} (c : f.Cell j) :
    (c.horn : SSet) ⟶ f.sigmaHorn j :=
  Sigma.ι (fun (c : f.Cell j) ↦ (c.horn : SSet)) c

/-- Given a rank function for a proper pairing of a subcomplex of a
simplicial set, this is coproduct of the standard simplices corresponding
to all cells of rank `j`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.sigmaStdSimplex** 是 Mathlib 中的一个缩写定义，位于命名
空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：sigmaStdSimplex (j : ι) : SSet.{u}
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank function for a proper pairing of a subcomplex of a
simplicial set, this is coproduct of the standard simplices corresponding
to all cells of rank `j`.
-/
noncomputable abbrev sigmaStdSimplex (j : ι) : SSet.{u} :=
  ∐ fun (i : f.Cell j) ↦ Δ[i.dim + 1]

variable {f} in
/-- Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the inclusion of
`Δ[c.dim + 1]` into `f.sigmaStdSimplex j`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.S
ubcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the inclusion of
`Δ[c.dim + 1]` into `f.sigmaStdSimplex j`.
-/
noncomputable abbrev Cell.ιSigmaStdSimplex {j : ι} (c : f.Cell j) :
    Δ[c.dim + 1] ⟶ f.sigmaStdSimplex j :=
  Sigma.ι (fun (c : f.Cell j) ↦ Δ[c.dim + 1]) c
/-
**SSet.Subcomplex.Pairing.RankFunction.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιSigmaHorn_jointly_surjective
    {d : ℕ} {j : ι} (a : (f.sigmaHorn j) _⦋d⦌) :
    ∃ (c : f.Cell j) (x : (c.horn : SSet) _⦋d⦌), c.ιSigmaHorn.app _ x = a :=
  Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
/-
**SSet.Subcomplex.Pairing.RankFunction.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιSigmaStdSimplex_jointly_surjective
    {d : ℕ} {j : ι} (a : (f.sigmaStdSimplex j) _⦋d⦌) :
    ∃ (c : f.Cell j) (x :  Δ[c.dim + 1] _⦋d⦌), c.ιSigmaStdSimplex.app _ x = a :=
  Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
/-
**SSet.Subcomplex.Pairing.RankFunction.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιSigmaStdSimplex_eq_iff {j : ι} {d : ℕ}
    (x : f.Cell j) (s : (Δ[x.dim + 1] : SSet.{u}) _⦋d⦌)
    (y : f.Cell j) (t : (Δ[y.dim + 1] : SSet.{u}) _⦋d⦌) :
    x.ιSigmaStdSimplex.app (op ⦋d⦌) s = y.ιSigmaStdSimplex.app (op ⦋d⦌) t ↔
      ∃ (h : x = y), t = cast (by rw [h]) s :=
  Cofan.inj_apply_eq_iff_of_isColimit
    (((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _)))) _ _
/-
**SSet.Subcomplex.Pairing.RankFunction.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcompl
ex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {j : ι} (c : f.Cell j) : Mono c.ιSigmaStdSimplex := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  intro x y h
  simpa [f.ιSigmaStdSimplex_eq_iff] using h.symm

/-- The coproduct of the horn inclusions corresponding to all the cells
of rank `j` for a rank function for a proper pairing of a subcomplex
of a simplicial set. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.m** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomp
lex.Pairing.RankFunction`。
形式化陈述：m (j : ι) : f.sigmaHorn j ⟶ f.sigmaStdSimplex j
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct of the horn inclusions corresponding to all the cells
of rank `j` for a rank function for a proper pairing of a subcomplex
of a simplicial set.
-/
noncomputable def m (j : ι) : f.sigmaHorn j ⟶ f.sigmaStdSimplex j :=
  Limits.Sigma.map (basicCell _ _)
/-
**SSet.Subcomplex.Pairing.RankFunction.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcompl
ex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : ι) : Mono (f.m j) := inferInstanceAs <| Mono (Limits.Sigma.map _)

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.ι_m {j : ι} (c : f.Cell j) :
    c.ιSigmaHorn ≫ f.m j = c.horn.ι ≫ c.ιSigmaStdSimplex := by
  simp [m]

@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.preimage_filtration_map** 是 Mathlib 
中的一个定理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst 
: LinearOrder ι] (f : P.RankFunction ι)   [inst_1 : P.IsProper] {j : ι} (c : f.C
ell j), (f.filtration j).preimage c.map = c.horn
参数：f : P.RankFunction ι；c : f.Cell j；f.filtration j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.Cell.image_face_index_compl`：image_
face_index_compl : (stdSimplex.face {c.index}ᶜ).image c.map = c.s.val.subcomplex
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.subcomplex_not_le_filtration`：
∀ {X : _root_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : Line
arOrder ι] {f : P.RankFunction ι}   {j : ι} (c : f.Cell j), …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.image_le_iff`：image_le_iff (Z : Y.Subcomplex) : A.image 
f <= Z ↔ A <= Z.preimage f
· 使用引理 `SSet.N.subcomplex_le_iff`：subcomplex_le_iff {A B : X.Subcomplex} : A <= 
B ↔ forall (s : X.N), s.subcomplex <= A -> s.subcomplex <= B
· 使用引理 `SSet.Subcomplex.N.cases`：cases {motive : X.N -> Prop} (mem : forall (s :
 X.N), s.subcomplex <= A -> motive s) (notMem : forall (s : A.N), motive s.toN) 
(s : X.N) : m…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `SSet.Subcomplex.Pairing.exists_or`：exists_or (x : A.N) : exists (y : P.I
I), x = y ∨ x = P.p y
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.rank_s`：∀ {X : _root_.SSet} {A
 : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f : P.Rank
Function ι}   {i : ι} (self : f.Cell i…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `SSet.Subcomplex.Pairing.le`：le [P.IsProper] (x : P.II) : x.1 <= (P.p x).
1
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.subcomplex_le_filtration`：subcomple
x_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) : (P.p c.s).val.subco
mplex <= f.filtration i
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.lt`：∀ {X : _root_.SSet} {A : X.Subc
omplex} {P : A.Pairing} {α : Type v} [inst : PartialOrder α] (self : P.RankFunct
ion α)   {x y : ↑P.II}, P.Anc…
· 使用引理 `SSet.S.le_def`：le_def {s t : X.S} : s <= t ↔ s.subcomplex <= t.subcomple
x
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.le`：le : x <= y
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.Cell.subcomplex_not_le_image_horn`：
subcomplex_not_le_image_horn : ¬ c.s.val.subcomplex <= c.horn.image c.map
· 使用引理 `SSet.Subcomplex.N.lt_iff`：lt_iff {x y : A.N} : x < y ↔ x.toN < y.toN
· 使用引理 `SSet.N.lt_iff`：lt_iff {x y : X.N} : x < y ↔ x.subcomplex < y.subcomplex
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.Cell.image_horn_lt_subcomplex`：imag
e_horn_lt_subcomplex : c.horn.image c.map < (P.p c.s).val.subcomplex
-/
lemma Cell.preimage_filtration_map {j : ι} (c : f.Cell j) :
    (f.filtration j).preimage c.map = c.horn := by
  apply le_antisymm
  · simpa only [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      Cell.image_face_index_compl] using c.subcomplex_not_le_filtration
  · rw [← Subcomplex.image_le_iff, N.subcomplex_le_iff]
    intro s hs
    cases s using N.cases A with
    | mem s hs' => exact hs'.trans (by simp)
    | notMem s =>
      obtain ⟨t, ht⟩ := P.exists_or s
      rw [← c.rank_s]
      refine le_trans ?_ (f.subcomplex_le_filtration ⟨t, rfl⟩ (f.lt ?_))
      · obtain rfl | rfl := ht
        · exact P.le t
        · simp
      · replace hs : t.val.subcomplex ≤ c.horn.image c.map := by
          obtain rfl | rfl := ht
          · exact hs
          · refine le_trans ?_ hs
            rw [← S.le_def]
            exact (P.isUniquelyCodimOneFace t).le
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact c.subcomplex_not_le_image_horn hs
        · rw [Subcomplex.N.lt_iff, SSet.N.lt_iff]
          exact lt_of_le_of_lt hs (c.image_horn_lt_subcomplex)

/-- Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the induced
morphism `c.horn ⟶ f.filtration j`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.mapHorn** 是 Mathlib 中的一个定义，位于命名空间 `S
Set.Subcomplex.Pairing.RankFunction.Cell`。
形式化陈述：{X : _root_.SSet} →   {A : X.Subcomplex} →     {P : A.Pairing} →       {ι 
: Type v} →         [inst : LinearOrder ι] →           (f : P.RankFunction ι) → 
            [inst_1 : P.IsProper] → {j : ι} → (c : f.Cell j) → c.horn.toSSet ⟶ (
f.filtration j).toSSet
参数：f : P.RankFunction ι；c : f.Cell j；f.filtration j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the induced
morphism `c.horn ⟶ f.filtration j`.
-/
noncomputable def Cell.mapHorn {j : ι} (c : f.Cell j) : (c.horn : SSet) ⟶ f.filtration j :=
  Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.mapHorn_** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.mapHorn_ι {j : ι} (c : f.Cell j) :
    c.mapHorn ≫ (f.filtration j).ι = c.horn.ι ≫ c.map := rfl

/-- Given a rank function `f : P.RankFunction ι` for a proper pairing `P`
of a subcomplex of a simplicial set, this is the induced morphism
`f.sigmaHorn j ⟶ f.filtration j` for any `j : ι`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.t** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomp
lex.Pairing.RankFunction`。
形式化陈述：t (j : ι) : f.sigmaHorn j ⟶ f.filtration j
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank function `f : P.RankFunction ι` for a proper pairing `P`
of a subcomplex of a simplicial set, this is the induced morphism
`f.sigmaHorn j ⟶ f.filtration j` for any `j : ι`.
-/
noncomputable def t (j : ι) : f.sigmaHorn j ⟶ f.filtration j :=
  Sigma.desc (fun c ↦ c.mapHorn)

variable {f} in
@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.ι_t {j : ι} (c : f.Cell j) : c.ιSigmaHorn ≫ f.t j = c.mapHorn := by
  simp [t]

variable {f} in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.ι_t_app {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ) :
    c.ιSigmaHorn.app x ≫ (f.t j).app x = c.mapHorn.app x :=
  NatTrans.congr_app c.ι_t x

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to `c.ιSigmaStdSimplex`. -/
@[simps]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.type** 是 Mathlib 中的一个定义，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to `c.ιSigmaStdSimplex`.
-/
noncomputable def Cell.type₁ {j : ι} (c : f.Cell j) : (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _ (stdSimplex.objEquiv.symm (𝟙 _))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply, ι_m, NatTrans.comp_app_apply, ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact objEquiv_symm_notMem_horn_of_isIso _ _ hy'

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to the `c.index`th-face of `c.type₁`. -/
@[simps]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.type** 是 Mathlib 中的一个定义，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to the `c.index`th-face of `c.type₁`.
-/
noncomputable def Cell.type₂ {j : ι} (c : f.Cell j) : (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply, ι_m, NatTrans.comp_app_apply, ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using (objEquiv_symm_δ_mem_horn_iff _ _).mp hy'

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.Pairing.RankFunction.exists_or_of_range_m_N** 是 Mathlib 中的一个引理
，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：exists_or_of_range_m_N {j : ι} (s : (Subcomplex.range (f.m j)).N) : exists
 (c : f.Cell j), s = c.type₁ ∨ s = c.type₂
参数：s : (Subcomplex.range (f.m j)).N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk_surjective`：mk_surjective (s : A.N) : exists (n : N
at) (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) (hx' : x ∉ A.obj _), s = mk x hx 
hx'
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.ιSigmaStdSimplex_jointly_surjective
`：ιSigmaStdSimplex_jointly_surjective {d : Nat} {j : ι} (a : (f.sigmaStdSimplex 
j) _⦋d⦌) : exists (c : f.Cell j) (x : Δ[c.dim + 1] _⦋d⦌), c.ιS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app_apply`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F G H : CategoryT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_m`：∀ {X : _root_.SSet} {A : 
X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] (f : P.RankFun
ction ι)   [inst_1 : P.IsProper] {j…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `SimplexCategory.le_of_mono`：le_of_mono {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono
 f] : n <= m
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `SSet.stdSimplex.mem_nonDegenerate_iff_mono`：mem_nonDegenerate_iff_mono {
n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) : s in Δ[n].nonDegenerate d ↔ Mono (objE
quiv s)
· 使用引理 `SSet.nonDegenerate_iff_of_mono`：nonDegenerate_iff_of_mono {Y : SSet.{u}}
 (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) : f.app _ x in Y.nonDegenerate n ↔ x in X.non
Degenerate n
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.instMonoιSigmaStdSimplex`：∀ {X : _r
oot_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι
] (f : P.RankFunction ι)   {j : ι} (c : f.Cell j), …
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `SSet.horn_obj_eq_univ`：horn_obj_eq_univ {n : Nat} (i : Fin (n + 1)) (m :
 Nat) (h : m + 1 < n
· 使用定理 `SimplexCategory.eq_δ_of_mono`：eq_δ_of_mono {n : Nat} (θ : ⦋n⦌ ⟶ ⦋n + 1⦌)
 [Mono θ] : exists i : Fin (n + 2), θ = δ i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SSet.objEquiv_symm_δ_notMem_horn_iff`：objEquiv_symm_δ_notMem_horn_iff {n
 : Nat} (i j : Fin (n + 2)) : (stdSimplex.objEquiv (m
· 使用定理 `SimplexCategory.eq_id_of_mono`：eq_id_of_mono {x : SimplexCategory} (i : 
x ⟶ x) [Mono i] : i = 𝟙 _
-/
lemma exists_or_of_range_m_N {j : ι} (s : (Subcomplex.range (f.m j)).N) :
    ∃ (c : f.Cell j), s = c.type₁ ∨ s = c.type₂ := by
  obtain ⟨d, s, hs, hs', rfl⟩ := s.mk_surjective
  obtain ⟨x, s, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective s
  replace hs' : s ∉ (horn _ x.index).obj _ :=
    fun h ↦ hs' ⟨x.ιSigmaHorn.app _ ⟨_, h⟩, by rw [← NatTrans.comp_app_apply]; simp⟩
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective s
  rw [nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply] at hs
  obtain hd | rfl := (SimplexCategory.le_of_mono g).lt_or_eq
  · rw [Nat.lt_succ_iff] at hd
    obtain hd | rfl := hd.lt_or_eq
    · exact (hs' (by simp [horn_obj_eq_univ x.index d (by lia)])).elim
    · obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono g
      obtain rfl := (objEquiv_symm_δ_notMem_horn_iff _ _).mp hs'
      exact ⟨x, Or.inr rfl⟩
  · obtain rfl := SimplexCategory.eq_id_of_mono g
    exact ⟨x, Or.inl rfl⟩

variable [SuccOrder ι] [NoMaxOrder ι]

/-- Given a rank function `f : P.RankFunction ι` for a proper pairing `P`
of a subcomplex of a simplicial set, this is the induced morphism
`f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j)` for any `j : ι`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.b** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomp
lex.Pairing.RankFunction`。
形式化陈述：b (j : ι) : f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j)
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank function `f : P.RankFunction ι` for a proper pairing `P`
of a subcomplex of a simplicial set, this is the induced morphism
`f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j)` for any `j : ι`.
-/
noncomputable def b (j : ι) : f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j) :=
  Sigma.desc (fun c ↦ c.mapToSucc)

variable {f} in
@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.ι_b {j : ι} (c : f.Cell j) : c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc := by
  simp [b]

variable {f} in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**SSet.Subcomplex.Pairing.RankFunction.Cell.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cell.ι_b_app {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ) :
    c.ιSigmaStdSimplex.app x ≫ (f.b j).app x = c.mapToSucc.app x :=
  NatTrans.congr_app c.ι_b x

@[reassoc]
/-
**SSet.Subcomplex.Pairing.RankFunction.w** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomp
lex.Pairing.RankFunction`。
形式化陈述：w (j : ι) : f.t j ≫ homOfLE (f.filtration_monotone (Order.le_succ j)) = f.
m j ≫ f.b j
参数：j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_t_assoc`：∀ {X : _root_.SSet}
 {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f : P.R
ankFunction ι}   [inst_1 : P.IsProper] {j…
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc`：∀ {X : _root_.SSet}
 {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] (f : P.R
ankFunction ι)   [inst_1 : P.IsProper] {j…
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_b`：∀ {X : _root_.SSet} {A : 
X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f : P.RankFun
ction ι}   [inst_1 : P.IsProper] [i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subfunctor.homOfLe_ι`：homOfLe_ι {G G' : Subfunctor F} (h 
: G <= G') : Subfunctor.homOfLe h ≫ G'.ι = G.ι
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma w (j : ι) :
    f.t j ≫ homOfLE (f.filtration_monotone (Order.le_succ j)) = f.m j ≫ f.b j := by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.Pairing.RankFunction.isPullback** 是 Mathlib 中的一个引理，位于命名空间 `SSe
t.Subcomplex.Pairing.RankFunction`。
形式化陈述：isPullback (j : ι) : IsPullback (f.t j) (f.m j) (homOfLE (f.filtration_mon
otone (Order.le_succ j))) (f.b j) where w
参数：j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.w`：w (j : ι) : f.t j ≫ homOfLE (f.f
iltration_monotone (Order.le_succ j)) = f.m j ≫ f.b j
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isPullback_iff`：∀ {X₁ X₂ X₃ X₄ : Type u} (t 
: X₁ ⟶ X₂) (r : X₂ ⟶ X₄) (l : X₁ ⟶ X₃) (b : X₃ ⟶ X₄),   CategoryTheory.IsPullbac
k t l r b ↔     CategoryTheory.C…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `CategoryTheory.NatTrans.mono_iff_mono_app`：∀ {K : Type u} [inst : Catego
ryTheory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v',
 u'} C]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.instMonoM`：∀ {X : _root_.SSet} {A :
 X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] (f : P.RankFu
nction ι)   [inst_1 : P.IsProper] (j…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.ιSigmaStdSimplex_jointly_surjective
`：ιSigmaStdSimplex_jointly_surjective {d : Nat} {j : ι} (a : (f.sigmaStdSimplex 
j) _⦋d⦌) : exists (c : f.Cell j) (x : Δ[c.dim + 1] _⦋d⦌), c.ιS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.preimage_filtration_map`：∀ {X 
: _root_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrd
er ι] (f : P.RankFunction ι)   [inst_1 : P.IsProper] {j…
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_b_app_apply`：∀ {X : _root_.S
Set} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f :
 P.RankFunction ι}   [inst_1 : P.IsProper] [i…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_t_app_apply`：∀ {X : _root_.S
Set} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f :
 P.RankFunction ι}   [inst_1 : P.IsProper] {j…
· 使用定理 `CategoryTheory.NatTrans.comp_app_apply`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F G H : CategoryT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_m`：∀ {X : _root_.SSet} {A : 
X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] (f : P.RankFun
ction ι)   [inst_1 : P.IsProper] {j…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
（共 31 条，此处仅展示前 30 条）
-/
lemma isPullback (j : ι) :
    IsPullback (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨d⟩⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).symm
      (IsPullback.isLimit ?_)
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌),
      fun a₁ a₂ h ↦ (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (f.m j)).mp inferInstance _) h.2, fun y b h ↦ ?_⟩
    obtain ⟨x, b, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective b
    have hb : b ∈ Λ[_, x.index].obj _ := by
      obtain ⟨y, hy⟩ := y
      simp only [← x.preimage_filtration_map]
      rw [Subtype.ext_iff] at h
      dsimp at h
      subst h
      rwa [x.ι_b_app_apply] at hy
    refine ⟨x.ιSigmaHorn.app _ ⟨b, hb⟩, ?_, ?_⟩
    · simpa only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
        x.ι_b_app_apply, x.ι_t_app_apply] using! h.symm
    · rw [← NatTrans.comp_app_apply]
      simp)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.Pairing.RankFunction.range_homOfLE_app_union_range_b_app** 是 M
athlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：range_homOfLE_app_union_range_b_app (j : ι) (d : SimplexCategoryᵒᵖ) : Set.
range ((homOfLE (f.filtration_monotone (Order.le_succ j))).app d) ⊔ Set.range ((
f.b j).app d) = Set.univ
参数：j : ι；d : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_b_assoc`：∀ {X : _root_.SSet}
 {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f : P.R
ankFunction ι}   [inst_1 : P.IsProper] [i…
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.mapToSucc_ι`：∀ {X : _root_.SSe
t} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] {f : P
.RankFunction ι}   [inst_1 : P.IsProper] {j…
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.Cell.range_map`：range_map : Subcomp
lex.range c.map = (P.p c.s).val.subcomplex
-/
lemma range_homOfLE_app_union_range_b_app (j : ι) (d : SimplexCategoryᵒᵖ) :
    Set.range ((homOfLE (f.filtration_monotone (Order.le_succ j))).app d) ⊔
      Set.range ((f.b j).app d) = Set.univ := by
  ext ⟨x, hx⟩
  -- generated by `simp? [filtration_def, Subtype.ext_iff] at hx ⊢`
  simp only [filtration_def, Order.lt_succ_iff, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, exists_prop, Subfunctor.toFunctor_obj, Subfunctor.homOfLe_app,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Set.sup_eq_union, Set.mem_range, Subtype.ext_iff,
    Subtype.exists, exists_eq_right, Set.mem_univ, iff_true] at hx ⊢
  obtain hx | ⟨i, hi, c, hx⟩ := hx
  · exact Or.inl (Or.inl hx)
  · obtain hi | rfl := hi.lt_or_eq
    · exact Or.inl (Or.inr ⟨i, hi, c, hx⟩)
    · rw [← c.range_map, ← c.mapToSucc_ι, ← c.ι_b_assoc] at hx
      obtain ⟨y, hy⟩ := hx
      exact Or.inr ⟨_, hy⟩

/-- Given a rank function `f : P.RankFunction ι` for a proper pairing
of a subcomplex of a simplicial set `X`, this is the simplex of `X`
corresponding to an element in `(Subcomplex.range (f.m j)).N`. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.mapN** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subc
omplex.Pairing.RankFunction`。
形式化陈述：mapN {j : ι} (x : (Subcomplex.range (f.m j)).N) : X.S
参数：x : (Subcomplex.range (f.m j)).N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a rank function `f : P.RankFunction ι` for a proper pairing
of a subcomplex of a simplicial set `X`, this is the simplex of `X`
corresponding to an element in `(Subcomplex.range (f.m j)).N`.
-/
noncomputable def mapN {j : ι} (x : (Subcomplex.range (f.m j)).N) : X.S :=
  S.mk ((f.b j).app _ x.simplex).val

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.mapN_type** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapN_type₁ {j : ι} (c : f.Cell j) : f.mapN c.type₁ = S.mk (P.p c.s).val.simplex := by
  dsimp only [Cell.type₁, mapN]
  rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp
  rw [S.ext_iff, c.ι_b_app_apply]
  apply yonedaEquiv_symm_app_id

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SSet.Subcomplex.Pairing.RankFunction.mapN_type** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapN_type₂ {j : ι} (c : f.Cell j) : f.mapN c.type₂ = S.mk c.s.val.simplex := by
  dsimp [mapN]
  rw [S.ext_iff, c.ι_b_app_apply, Cell.mapToSucc]
  exact c.map_app_objEquiv_symm_δ_index
/-
**SSet.Subcomplex.Pairing.RankFunction.isPushout_aux** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isPushout_aux₁ {j : ι} (s : (Subcomplex.range (f.m j)).N) :
    (f.mapN s).simplex  ∈ SSet.nonDegenerate _ _ := by
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s
  · rw [f.mapN_type₁]
    exact (P.p c.s).val.nonDegenerate
  · rw [f.mapN_type₂]
    exact c.s.val.nonDegenerate
/-
**SSet.Subcomplex.Pairing.RankFunction.isPushout_aux** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isPushout_aux₂ {j : ι} : Function.Injective (f.mapN (j := j)) := by
  intro s t h
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s <;>
    obtain ⟨c', rfl | rfl⟩ := f.exists_or_of_range_m_N t <;>
    simp only [mapN_type₁, mapN_type₂, ← Subcomplex.N.eq_iff_sMk_eq,
      ← Subtype.ext_iff] at h
  · obtain rfl : c = c' := by ext : 1; exact P.p.injective h
    rfl
  · exact (P.ne _ _ h).elim
  · exact (P.ne _ _ h.symm).elim
  · congr; aesop
/-
**SSet.Subcomplex.Pairing.RankFunction.isPushout_aux** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isPushout_aux₃ {j : ι} :
    Function.Injective fun (x : (Subcomplex.range (f.m j)).N) ↦ S.mk ((f.b j).app _ x.simplex) :=
  fun _ _ h ↦ f.isPushout_aux₂ (congr_arg (S.map (Subcomplex.ι _)) h)

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.Pairing.RankFunction.isPushout** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction`。
形式化陈述：isPushout (j : ι) : IsPushout (f.t j) (f.m j) (homOfLE (f.filtration_monot
one (Order.le_succ j))) (f.b j) where w
参数：j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.w`：w (j : ι) : f.t j ≫ homOfLE (f.f
iltration_monotone (Order.le_succ j)) = f.m j ≫ f.b j
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'`：isPushout_
of_isPullback_of_mono' (h₁ : IsPullback t l r b) [Mono r] (h₂ : Set.range r ⊔ Se
t.range b = Set.univ) (H : forall (x₃ y₃ : X₃) (_ …
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.isPullback`：isPullback (j : ι) : Is
Pullback (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.
b j) where w
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.range_homOfLE_app_union_range_b_app
`：range_homOfLE_app_union_range_b_app (j : ι) (d : SimplexCategoryᵒᵖ) : Set.rang
e ((homOfLE (f.filtration_monotone (Order.le_succ j))).app d) …
· 使用引理 `SSet.Subcomplex.existsN`：existsN {X : SSet.{u}} {n : Nat} (s : X _⦋n⦌) {
A : X.Subcomplex} (hs : s ∉ A.obj _) : exists (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi
 f ∧ X.map f.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.unique_nonDegenerate_map`：unique_nonDegenerate_map (x : X _⦋n⦌) {m 
: Nat} (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op
 y₁) (f₂ : ⦋n⦌ ⟶ ⦋m…
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Relat
iveCellComplex.0.SSet.Subcomplex.Pairing.RankFunction.isPushout_aux₁`：∀ {X : _ro
ot_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι]
 (f : P.RankFunction ι)   [inst_1 : P.IsProper] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Relat
iveCellComplex.0.SSet.Subcomplex.Pairing.RankFunction.isPushout_aux₃`：∀ {X : _ro
ot_.SSet} {A : X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι]
 (f : P.RankFunction ι)   [inst_1 : P.IsProper] [i…
· 使用引理 `SSet.S.eq_iff_ofSimplex_eq`：eq_iff_ofSimplex_eq {X : SSet.{u}} {n m : Na
t} (x : X _⦋n⦌) (y : X _⦋m⦌) (hx : x in X.nonDegenerate _) (hy : y in X.nonDegen
erate _) : S.mk …
· 使用引理 `SSet.Subcomplex.mem_nonDegenerate_iff`：mem_nonDegenerate_iff {n : Nat} (
x : A.obj (op ⦋n⦌)) : dsimp% x in nonDegenerate A n ↔ x.val in X.nonDegenerate n
· 使用引理 `SSet.Subcomplex.ofSimplex_map_of_epi`：ofSimplex_map_of_epi {X : SSet.{u}
} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] (x : X _⦋m⦌) : ofSimplex (X.map f.op x) = 
ofSimplex x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma isPushout (j : ι) :
    IsPushout (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).symm
      (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j).map ((CategoryTheory.evaluation _ _).obj _))
      (f.range_homOfLE_app_union_range_b_app _ _) (fun x₁ x₂ hx₁ hx₂ h ↦ ?_)
    obtain ⟨s₁, g₁, _, hg₁⟩ := (Subcomplex.range (f.m j)).existsN x₁ hx₁
    obtain ⟨s₂, g₂, _, hg₂⟩ := (Subcomplex.range (f.m j)).existsN x₂ hx₂
    obtain rfl : s₁ = s₂ := f.isPushout_aux₃ (by
      dsimp
      rw [S.eq_iff_ofSimplex_eq, ← Subcomplex.ofSimplex_map_of_epi g₁,
        ← Subcomplex.ofSimplex_map_of_epi g₂]
      · simp [← dsimp% (f.b j).naturality_apply, hg₁, hg₂, dsimp% h]
      all_goals
      · rw [Subcomplex.mem_nonDegenerate_iff]
        apply f.isPushout_aux₁)
    obtain rfl := X.unique_nonDegenerate_map (x := (((f.b _)).app _ x₁).val)
      g₁ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, ← hg₁, dsimp% NatTrans.naturality_apply (f.b j)])
      g₂ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, dsimp% h, ← hg₂, dsimp% NatTrans.naturality_apply (f.b j)])
    rw [← hg₁, hg₂])⟩

end

variable [SuccOrder ι] [OrderBot ι] [NoMaxOrder ι] [WellFoundedLT ι]

/-
**SSet.Subcomplex.Pairing.RankFunction.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcompl
ex.Pairing.RankFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : f.filtration_monotone.functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

/-- Given a rank function `f : P.RankFunction ι` for a
proper pairing `P` of a subcomplex `A` of simplicial set `X`,
the inclusion `A.ι` is a relative cell complex with basic cells
given by horn inclusions. -/
/-
**SSet.Subcomplex.Pairing.RankFunction.relativeCellComplex** 是 Mathlib 中的一个定义，位于
命名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：relativeCellComplex : RelativeCellComplex f.basicCell A.ι where F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_monotone`：filtration_mon
otone : Monotone f.filtration
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.filtration_bot`：filtration_bot [Ord
erBot ι] : f.filtration ⊥ = A
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.Cell.ι_m`：∀ {X : _root_.SSet} {A : 
X.Subcomplex} {P : A.Pairing} {ι : Type v} [inst : LinearOrder ι] (f : P.RankFun
ction ι)   [inst_1 : P.IsProper] {j…
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.isPushout`：isPushout (j : ι) : IsPu
shout (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j
) where w

--- 原说明 ---
Given a rank function `f : P.RankFunction ι` for a
proper pairing `P` of a subcomplex `A` of simplicial set `X`,
the inclusion `A.ι` is a relative cell complex with basic cells
given by horn inclusions.
-/
noncomputable def relativeCellComplex :
    RelativeCellComplex f.basicCell A.ι where
  F := f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocone.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
  incl.app i := (f.filtration i).ι
  attachCells j _ :=
    { ι := f.Cell j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ι_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j }

end SSet.Subcomplex.Pairing.RankFunction

