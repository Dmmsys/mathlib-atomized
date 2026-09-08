/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Degenerate simplices

Given a simplicial set `X` and `n : ℕ`, we define the sets `X.degenerate n`
and `X.nonDegenerate n` of degenerate or non-degenerate simplices of dimension `n`.

Any simplex `x : X _⦋n⦌` can be written in a unique way as `X.map f.op y`
for an epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌` and a non-degenerate `m`-simplex `y`
(see lemmas `exists_nonDegenerate`, `unique_nonDegenerate_dim`,
`unique_nonDegenerate_simplex` and `unique_nonDegenerate_map`).

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

/-- An `n`-simplex of a simplicial set `X` is degenerate if it is in the range
of `X.map f.op` for some morphism `f : [n] ⟶ [m]` with `m < n`. -/
/-
**SSet.degenerate** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：degenerate (n : Nat) : Set (X _⦋n⦌)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n`-simplex of a simplicial set `X` is degenerate if it is in the range
of `X.map f.op` for some morphism `f : [n] ⟶ [m]` with `m < n`.
-/
def degenerate (n : ℕ) : Set (X _⦋n⦌) :=
  Set.ofPred (fun x ↦ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x ∈ Set.range (X.map f.op))

/-- The set of `n`-dimensional non-degenerate simplices in a simplicial
set `X` is the complement of `X.degenerate n`. -/
/-
**SSet.nonDegenerate** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：nonDegenerate (n : Nat) : Set (X _⦋n⦌)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of `n`-dimensional non-degenerate simplices in a simplicial
set `X` is the complement of `X.degenerate n`.
-/
def nonDegenerate (n : ℕ) : Set (X _⦋n⦌) := (X.degenerate n)ᶜ

@[simp]
/-
**SSet.degenerate_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：degenerate_zero : X.degenerate 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma degenerate_zero : X.degenerate 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
/-
**SSet.nondegenerate_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：nondegenerate_zero : X.nonDegenerate 0 = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.degenerate_zero`：degenerate_zero : X.degenerate 0 = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nondegenerate_zero : X.nonDegenerate 0 = Set.univ := by
  simp [nonDegenerate]

variable {n : ℕ}
/-
**SSet.mem_nonDegenerate_iff_notMem_degenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_nonDegenerate_iff_notMem_degenerate (x : X _⦋n⦌) : x in X.nonDegenerat
e n ↔ x ∉ X.degenerate n
参数：x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nonDegenerate_iff_notMem_degenerate (x : X _⦋n⦌) :
    x ∈ X.nonDegenerate n ↔ x ∉ X.degenerate n := Iff.rfl
/-
**SSet.mem_degenerate_iff_notMem_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_degenerate_iff_notMem_nonDegenerate (x : X _⦋n⦌) : x in X.degenerate n
 ↔ x ∉ X.nonDegenerate n
参数：x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_degenerate_iff_notMem_nonDegenerate (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ x ∉ X.nonDegenerate n := by
  simp [nonDegenerate]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _⦋n⦌) :
    X.σ i x ∈ X.degenerate (n + 1) :=
  ⟨n, by lia, SimplexCategory.σ i, Set.mem_range_self x⟩
/-
**SSet.mem_degenerate_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_degenerate_iff (x : X _⦋n⦌) : x in X.degenerate n ↔ exists (m : Nat) (
_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f), x in Set.range (X.map f.op)
参数：x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `SimplexCategory.instHasStrongEpiMonoFactorisations`：CategoryTheory.Limit
s.HasStrongEpiMonoFactorisations SimplexCategory
· 使用定理 `SimplexCategory.len_le_of_mono`：len_le_of_mono {x y : SimplexCategory} (
f : x ⟶ y) [Mono f] : x.len <= y.len
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `SimplexCategory.instEpiFactorThruImage`：∀ (Δ Δ' : SimplexCategory) (θ : 
Δ ⟶ Δ'), CategoryTheory.Epi (CategoryTheory.Limits.factorThruImage θ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
-/
lemma mem_degenerate_iff (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f, op_comp] at hy
    have : _ ≤ m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by lia, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.opObjEquiv_mem_degenerate_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：opObjEquiv_mem_degenerate_iff (x : X.op _⦋n⦌) : opObjEquiv x in X.degenera
te n ↔ x in X.op.degenerate n
参数：x : X.op _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `SimplexCategory.instIsEquivalenceRev`：SimplexCategory.rev.IsEquivalence
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用引理 `SimplexCategory.rev_map_rev_map`：rev_map_rev_map {n m : SimplexCategory}
 (f : n ⟶ m) : rev.map (rev.map f) = f
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opObjEquiv_mem_degenerate_iff (x : X.op _⦋n⦌) :
    opObjEquiv x ∈ X.degenerate n ↔ x ∈ X.op.degenerate n := by
  simp only [mem_degenerate_iff]
  refine exists_congr (fun m ↦ exists_congr (fun _ ↦ ?_))
  constructor
  · obtain ⟨x, rfl⟩ := opObjEquiv.symm.surjective x
    rintro ⟨f, _, y, rfl⟩
    exact ⟨SimplexCategory.rev.map f, inferInstance, opObjEquiv.symm y, by simp [op_map]⟩
  · rintro ⟨f, _, y, rfl⟩
    exact ⟨SimplexCategory.rev.map f, inferInstance, opObjEquiv y, by simp [op_map]⟩
/-
**SSet.opObjEquiv_mem_nonDegenerate_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：opObjEquiv_mem_nonDegenerate_iff (x : X.op _⦋n⦌) : opObjEquiv x in X.nonDe
generate n ↔ x in X.op.nonDegenerate n
参数：x : X.op _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma opObjEquiv_mem_nonDegenerate_iff (x : X.op _⦋n⦌) :
    opObjEquiv x ∈ X.nonDegenerate n ↔ x ∈ X.op.nonDegenerate n := by
  simp only [mem_nonDegenerate_iff_notMem_degenerate,
    opObjEquiv_mem_degenerate_iff]
/-
**SSet.degenerate_eq_iUnion_range_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma degenerate_eq_iUnion_range_σ :
    X.degenerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf ↦ by
      rw [← SimplexCategory.mono_iff_injective] at hf
      have := SimplexCategory.le_of_mono f
      lia)
    aesop
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate
/-
**SSet.exists_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：exists_nonDegenerate (x : X _⦋n⦌) : exists (m : Nat) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : 
Epi f) (y : X.nonDegenerate m), x = X.map f.op y
参数：x : X _⦋n⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.nondegenerate_zero`：nondegenerate_zero : X.nonDegenerate 0 = Set.un
iv
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.degenerate_eq_iUnion_range_σ`：degenerate_eq_iUnion_range_σ : X.dege
nerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimplexCategory.instEpiσ`：∀ {n : ℕ} {i : Fin (n + 1)}, CategoryTheory.Ep
i (SimplexCategory.σ i)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_nonDegenerate (x : X _⦋n⦌) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y := by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x ∈ X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩
/-
**SSet.isIso_of_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：isIso_of_nonDegenerate (x : X.nonDegenerate n) {m : SimplexCategory} (f : 
⦋n⦌ ⟶ m) [Epi f] (y : X.obj (op m)) (hy : X.map f.op y = x) : IsIso f
参数：x : X.nonDegenerate n；f : ⦋n⦌ ⟶ m；y : X.obj (op m)；hy : X.map f.op y = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.mem_nonDegenerate_iff_notMem_degenerate`：mem_nonDegenerate_iff_notM
em_degenerate (x : X _⦋n⦌) : x in X.nonDegenerate n ↔ x ∉ X.degenerate n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `SimplexCategory.isIso_iff_of_epi`：isIso_iff_of_epi {n m : SimplexCategor
y} (f : n ⟶ m) [hf : Epi f] : IsIso f ↔ n.len = m.len
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimplexCategory.len_le_of_epi`：len_le_of_epi {x y : SimplexCategory} (f 
: x ⟶ y) [Epi f] : y.len <= x.len
-/
lemma isIso_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction m using SimplexCategory.rec with | _ m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra hf
  refine hx ⟨_, not_le.1 (fun h ↦ hf ?_), f, y, hy⟩
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm h (SimplexCategory.len_le_of_epi f)
/-
**SSet.mono_of_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mono_of_nonDegenerate (x : X.nonDegenerate n) {m : SimplexCategory} (f : ⦋
n⦌ ⟶ m) (y : X.obj (op m)) (hy : X.map f.op y = x) : Mono f
参数：x : X.nonDegenerate n；f : ⦋n⦌ ⟶ m；y : X.obj (op m)；hy : X.map f.op y = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `SimplexCategory.instHasStrongEpiMonoFactorisations`：CategoryTheory.Limit
s.HasStrongEpiMonoFactorisations SimplexCategory
· 使用引理 `SSet.isIso_of_nonDegenerate`：isIso_of_nonDegenerate (x : X.nonDegenerate
 n) {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) [Epi f] (y : X.obj (op m)) (hy : X.map f
.op y = x) : IsIs…
· 使用定理 `SimplexCategory.instEpiFactorThruImage`：∀ (Δ Δ' : SimplexCategory) (θ : 
Δ ⟶ Δ'), CategoryTheory.Epi (CategoryTheory.Limits.factorThruImage θ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
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
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
-/
lemma mono_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m)
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    Mono f := by
  have := X.isIso_of_nonDegenerate x (factorThruImage f) (y := X.map (image.ι f).op y) (by
      rw [← comp_apply, ← Functor.map_comp, ← op_comp, image.fac f, hy])
  rw [← image.fac f]
  infer_instance

namespace unique_nonDegenerate

/-!
Auxiliary definitions and lemmas for the lemmas
`unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` and
`unique_nonDegenerate_map` which assert the uniqueness of the
decomposition obtained in the lemma `exists_nonDegenerate`.
-/

section

variable {X} {x : X _⦋n⦌}
  {m₁ m₂ : ℕ} {f₁ : ⦋n⦌ ⟶ ⦋m₁⦌} (hf₁ : SplitEpi f₁)
  (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
  (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) (y₂ : X _⦋m₂⦌) (hy₂ : x = X.map f₂.op y₂)

/-- The composition of a section of `f₁` and `f₂`. It is proven below that it
is the identity, see `g_eq_id`. -/
/-
**SSet.unique_nonDegenerate.g** 是 Mathlib 中的一个定义，位于命名空间 `SSet.unique_nonDegenera
te`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of a section of `f₁` and `f₂`. It is proven below that it
is the identity, see `g_eq_id`.
-/
private def g := hf₁.section_ ≫ f₂

variable {f₂ y₁ y₂}

include hf₁ hy₁ hy₂
/-
**SSet.unique_nonDegenerate.map_g_op_y** 是 Mathlib 中的一个引理，位于命名空间 `SSet.unique_no
nDegenerate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma map_g_op_y₂ : X.map (g hf₁ f₂).op y₂ = y₁ := by
  dsimp [g]
  rw [Functor.map_comp, comp_apply, ← hy₂, hy₁, ← comp_apply, ← Functor.map_comp, ← op_comp,
    SplitEpi.id, op_id, CategoryTheory.Functor.map_id, id_apply]
/-
**SSet.unique_nonDegenerate.isIso_factorThruImage_g** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.unique_nonDegenerate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isIso_factorThruImage_g :
    IsIso (factorThruImage (g hf₁ f₂)) := by
  have := map_g_op_y₂ hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂), op_comp, Functor.map_comp, comp_apply] at this
  exact X.isIso_of_nonDegenerate y₁ (factorThruImage (g hf₁ f₂)) _ this
/-
**SSet.unique_nonDegenerate.mono_g** 是 Mathlib 中的一个引理，位于命名空间 `SSet.unique_nonDeg
enerate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mono_g : Mono (g hf₁ f₂) := by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]
  infer_instance
/-
**SSet.unique_nonDegenerate.le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.unique_nonDegener
ate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le : m₁ ≤ m₂ :=
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  SimplexCategory.len_le_of_mono
    (factorThruImage (g hf₁ f₂) ≫ image.ι _)

end

variable {X} in
/-
**SSet.unique_nonDegenerate.g_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.unique_nonDe
generate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma g_eq_id {x : X _⦋n⦌} {m : ℕ} {f₁ : ⦋n⦌ ⟶ ⦋m⦌}
    {y₁ : X.nonDegenerate m} (hy₁ : x = X.map f₁.op y₁)
    {f₂ : ⦋n⦌ ⟶ ⦋m⦌} {y₂ : X _⦋m⦌} (hy₂ : x = X.map f₂.op y₂) (hf₁ : SplitEpi f₁) :
    g hf₁ f₂ = 𝟙 _ := by
  have := mono_g hf₁ hy₁ hy₂
  apply SimplexCategory.eq_id_of_mono

end unique_nonDegenerate

section

open unique_nonDegenerate

/-!
The following lemmas `unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` and
`unique_nonDegenerate_map` assert the uniqueness of the decomposition
obtained in the lemma `exists_nonDegenerate`.
-/

/-
**SSet.unique_nonDegenerate_dim** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：unique_nonDegenerate_dim (x : X _⦋n⦌) {m₁ m₂ : Nat} (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi
 f₁] (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁) (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi
 f₂] (y₂ : X.nonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) : m₁ = m₂
参数：x : X _⦋n⦌；f₁ : ⦋n⦌ ⟶ ⦋m₁⦌；y₁ : X.nonDegenerate m₁；hy₁ : x = X.map f₁.op y₁；f
₂ : ⦋n⦌ ⟶ ⦋m₂⦌；y₂ : X.nonDegenerate m₂；hy₂ : x = X.map f₂.op y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.Degenerate.0.SSet.uniqu
e_nonDegenerate.le`：∀ {X : _root_.SSet} {n : ℕ} {x : X.obj (Opposite.op { len :=
 n })} {m₁ m₂ : ℕ} {f₁ : { len := n } ⟶ { len := m₁ }}   (hf₁ : CategoryTheory.S
…

--- 原说明 ---
The following lemmas `unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` 
and
`unique_nonDegenerate_map` assert the uniqueness of the decomposition
obtained in the lemma `exists_nonDegenerate`.
-/
lemma unique_nonDegenerate_dim (x : X _⦋n⦌) {m₁ m₂ : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi f₁] (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi f₂] (y₂ : X.nonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) :
    m₁ = m₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  obtain ⟨⟨hf₂⟩⟩ := isSplitEpi_of_epi f₂
  exact le_antisymm (le hf₁ hy₁ hy₂) (le hf₂ hy₂ hy₁)
/-
**SSet.unique_nonDegenerate_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：unique_nonDegenerate_simplex (x : X _⦋n⦌) {m : Nat} (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi 
f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁) (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X
.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) : y₁ = y₂
参数：x : X _⦋n⦌；f₁ : ⦋n⦌ ⟶ ⦋m⦌；y₁ : X.nonDegenerate m；hy₁ : x = X.map f₁.op y₁；f₂ 
: ⦋n⦌ ⟶ ⦋m⦌；y₂ : X.nonDegenerate m；hy₂ : x = X.map f₂.op y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.Degenerate.0.SSet.uniqu
e_nonDegenerate.g_eq_id`：∀ {X : _root_.SSet} {n : ℕ} {x : X.obj (Opposite.op { l
en := n })} {m : ℕ} {f₁ : { len := n } ⟶ { len := m }}   {y₁ : ↑(X.nonDegenerate
 m)},…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.Degenerate.0.SSet.uniqu
e_nonDegenerate.map_g_op_y₂`：∀ {X : _root_.SSet} {n : ℕ} {x : X.obj (Opposite.op
 { len := n })} {m₁ m₂ : ℕ} {f₁ : { len := n } ⟶ { len := m₁ }}   (hf₁ : Categor
yTheory.S…
-/
lemma unique_nonDegenerate_simplex (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    y₁ = y₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  ext
  simpa [g_eq_id hy₁ hy₂ hf₁] using (map_g_op_y₂ hf₁ hy₁ hy₂).symm
/-
**SSet.unique_nonDegenerate_map** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：unique_nonDegenerate_map (x : X _⦋n⦌) {m : Nat} (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] 
(y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁) (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.non
Degenerate m) (hy₂ : x = X.map f₂.op y₂) : f₁ = f₂
参数：x : X _⦋n⦌；f₁ : ⦋n⦌ ⟶ ⦋m⦌；y₁ : X.nonDegenerate m；hy₁ : x = X.map f₁.op y₁；f₂ 
: ⦋n⦌ ⟶ ⦋m⦌；y₂ : X.nonDegenerate m；hy₂ : x = X.map f₂.op y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `SimplexCategory.congr_toOrderHom_apply`：congr_toOrderHom_apply {a b : Si
mplexCategory} {f g : a ⟶ b} (h : f = g) (x : Fin (a.len + 1)) : f.toOrderHom x 
= g.toOrderHom x
· 使用定理 `CategoryTheory.SplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.SplitEpi f),   Cate
goryTheory.Categ…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `OrderHom.mk.congr_simp`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder
 α] [inst_1 : Preorder β] (toFun toFun_1 : α → β)   (e_toFun : toFun = toFun_1) 
(monotone' :…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.Degenerate.0.SSet.uniqu
e_nonDegenerate.g_eq_id`：∀ {X : _root_.SSet} {n : ℕ} {x : X.obj (Opposite.op { l
en := n })} {m : ℕ} {f₁ : { len := n } ⟶ { len := m }}   {y₁ : ↑(X.nonDegenerate
 m)},…
-/
lemma unique_nonDegenerate_map (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    f₁ = f₂ := by
  ext x : 3
  suffices ∃ (hf₁ : SplitEpi f₁), hf₁.section_.toOrderHom (f₁.toOrderHom x) = x by
    obtain ⟨hf₁, hf₁'⟩ := this
    dsimp at hf₁'
    simpa [g, hf₁'] using (SimplexCategory.congr_toOrderHom_apply (g_eq_id hy₁ hy₂ hf₁)
      (f₁.toOrderHom x)).symm
  obtain ⟨⟨hf⟩⟩ := isSplitEpi_of_epi f₁
  let α (y : Fin (m + 1)) : Fin (n + 1) :=
    if y = f₁.toOrderHom x then x else hf.section_.toOrderHom y
  have hα₁ (y : Fin (m + 1)) : f₁.toOrderHom (α y) = y := by
    dsimp [α]
    split_ifs with hy
    · rw [hy]
    · apply SimplexCategory.congr_toOrderHom_apply hf.id
  have hα₂ : Monotone α := by
    rintro y₁ y₂ h
    by_contra! h'
    suffices y₂ ≤ y₁ by simp [show y₁ = y₂ by lia] at h'
    simpa only [hα₁] using f₁.toOrderHom.monotone h'.le
  exact ⟨{ section_ := SimplexCategory.Hom.mk ⟨α, hα₂⟩, id := by ext : 3; apply hα₁ },
    by simp [α]⟩

end

namespace Subcomplex

variable {X} (A : X.Subcomplex)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.mem_degenerate_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`
。
形式化陈述：mem_degenerate_iff {n : Nat} (x : A.obj (op ⦋n⦌)) : dsimp% x in degenerate
 A n ↔ x.val in X.degenerate n
参数：x : A.obj (op ⦋n⦌)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.mem_degenerate_iff`：mem_degenerate_iff (x : X _⦋n⦌) : x in X.degene
rate n ↔ exists (m : Nat) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f), x in Set.rang
e (X.map f.op…
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `CategoryTheory.Subfunctor.map`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (self : CategoryTheory
.Subfunctor F) {U V…
-/
lemma mem_degenerate_iff {n : ℕ} (x : A.obj (op ⦋n⦌)) :
    dsimp% x ∈ degenerate A n ↔ x.val ∈ X.degenerate n := by
  rw [SSet.mem_degenerate_iff, SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, _, y, rfl⟩
    exact ⟨m, hm, f, inferInstance, y.val, rfl⟩
  · obtain ⟨x, hx⟩ := x
    rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    refine ⟨m, hm, f, inferInstance, ⟨y, ?_⟩, rfl⟩
    have := isSplitEpi_of_epi f
    simpa [Set.mem_preimage, ← op_comp, ← comp_apply, ← Functor.map_comp] using
      A.map (section_ f).op hx

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.mem_nonDegenerate_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：mem_nonDegenerate_iff {n : Nat} (x : A.obj (op ⦋n⦌)) : dsimp% x in nonDege
nerate A n ↔ x.val in X.nonDegenerate n
参数：x : A.obj (op ⦋n⦌)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.mem_nonDegenerate_iff_notMem_degenerate`：mem_nonDegenerate_iff_notM
em_degenerate (x : X _⦋n⦌) : x in X.nonDegenerate n ↔ x ∉ X.degenerate n
· 使用引理 `SSet.Subcomplex.mem_degenerate_iff`：mem_degenerate_iff {n : Nat} (x : A.
obj (op ⦋n⦌)) : dsimp% x in degenerate A n ↔ x.val in X.degenerate n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nonDegenerate_iff {n : ℕ} (x : A.obj (op ⦋n⦌)) :
    dsimp% x ∈ nonDegenerate A n ↔ x.val ∈ X.nonDegenerate n := by
  rw [mem_nonDegenerate_iff_notMem_degenerate,
    mem_nonDegenerate_iff_notMem_degenerate, mem_degenerate_iff]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.le_iff_contains_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
Subcomplex`。
形式化陈述：le_iff_contains_nonDegenerate (B : X.Subcomplex) : A <= B ↔ forall (n : Na
t) (x : X.nonDegenerate n), x.val in A.obj _ -> x.val in B.obj _
参数：B : X.Subcomplex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.exists_nonDegenerate`：exists_nonDegenerate (x : X _⦋n⦌) : exists (m
 : Nat) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f) (y : X.nonDegenerate m), x = X.map f.op y
· 使用定理 `CategoryTheory.Subfunctor.map`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (self : CategoryTheory
.Subfunctor F) {U V…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.mem_nonDegenerate_iff`：mem_nonDegenerate_iff {n : Nat} (
x : A.obj (op ⦋n⦌)) : dsimp% x in nonDegenerate A n ↔ x.val in X.nonDegenerate n
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma le_iff_contains_nonDegenerate (B : X.Subcomplex) :
    A ≤ B ↔ ∀ (n : ℕ) (x : X.nonDegenerate n), x.val ∈ A.obj _ → x.val ∈ B.obj _ := by
  constructor
  · aesop
  · rintro h ⟨n⟩ x hx
    induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, f, _, ⟨a, ha⟩, ha'⟩ := exists_nonDegenerate A ⟨x, hx⟩
    simp only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
      Subfunctor.toFunctor_map] at ha'
    subst ha'
    rw [mem_nonDegenerate_iff] at ha
    exact B.map f.op (h _ ⟨_, ha⟩ a.prop)
/-
**SSet.Subcomplex.eq_top_iff_contains_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.Subcomplex`。
形式化陈述：eq_top_iff_contains_nonDegenerate : A = ⊤ ↔ forall (n : Nat), X.nonDegener
ate n subseteq A.obj _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `SSet.Subcomplex.le_iff_contains_nonDegenerate`：le_iff_contains_nonDegene
rate (B : X.Subcomplex) : A <= B ↔ forall (n : Nat) (x : X.nonDegenerate n), x.v
al in A.obj _ -> x.val in B.obj _
-/
lemma eq_top_iff_contains_nonDegenerate :
    A = ⊤ ↔ ∀ (n : ℕ), X.nonDegenerate n ⊆ A.obj _ := by
  simpa using! le_iff_contains_nonDegenerate ⊤ A

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.degenerate_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：degenerate_eq_top_iff (n : Nat) : degenerate A n = ⊤ ↔ (X.degenerate n ⊓ A
.obj _) = A.obj _
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.mem_degenerate_iff`：mem_degenerate_iff {n : Nat} (x : A.
obj (op ⦋n⦌)) : dsimp% x in degenerate A n ↔ x.val in X.degenerate n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma degenerate_eq_top_iff (n : ℕ) :
    degenerate A n = ⊤ ↔ (X.degenerate n ⊓ A.obj _) = A.obj _ := by
  constructor
  · intro h
    ext x
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    simp [← A.mem_degenerate_iff ⟨x, hx⟩, h, Set.top_eq_univ, Set.mem_univ]
  · intro h
    simp only [Set.inf_eq_inter, Set.inter_eq_right] at h
    ext x
    simpa [A.mem_degenerate_iff] using h x.prop

variable (X) in
/-
**SSet.Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.Subcomplex`。
形式化陈述：iSup_ofSimplex_nonDegenerate_eq_top : ⨆ (x : Σ (p : Nat), X.nonDegenerate 
p), ofSimplex x.2.val = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.eq_top_iff_contains_nonDegenerate`：eq_top_iff_contains_n
onDegenerate : A = ⊤ ↔ forall (n : Nat), X.nonDegenerate n subseteq A.obj _
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `SSet.Subcomplex.mem_ofSimplex_obj`：mem_ofSimplex_obj {n : Nat} (x : X _⦋
n⦌) : x in (ofSimplex x).obj _
-/
lemma iSup_ofSimplex_nonDegenerate_eq_top :
    ⨆ (x : Σ (p : ℕ), X.nonDegenerate p), ofSimplex x.2.val = ⊤ := by
  rw [eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop]
  exact ⟨n, x, hx, mem_ofSimplex_obj x⟩

end Subcomplex

section

variable {X} {Y : SSet.{u}}

/-
**SSet.degenerate_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：degenerate_app_apply {n : Nat} {x : X _⦋n⦌} (hx : x in X.degenerate n) (f 
: X ⟶ Y) : f.app _ x in Y.degenerate n
参数：hx : x in X.degenerate n；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma degenerate_app_apply {n : ℕ} {x : X _⦋n⦌} (hx : x ∈ X.degenerate n) (f : X ⟶ Y) :
    f.app _ x ∈ Y.degenerate n := by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, g, f.app _ y, by rw [NatTrans.naturality_apply]⟩
/-
**SSet.degenerate_le_preimage** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：degenerate_le_preimage (f : X ⟶ Y) (n : Nat) : X.degenerate n subseteq (f.
app _) ⁻¹' (Y.degenerate n)
参数：f : X ⟶ Y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.degenerate_app_apply`：degenerate_app_apply {n : Nat} {x : X _⦋n⦌} (
hx : x in X.degenerate n) (f : X ⟶ Y) : f.app _ x in Y.degenerate n
-/
lemma degenerate_le_preimage (f : X ⟶ Y) (n : ℕ) :
    X.degenerate n ⊆ (f.app _) ⁻¹' (Y.degenerate n) :=
  fun _ hx ↦ degenerate_app_apply hx f
/-
**SSet.image_degenerate_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：image_degenerate_le (f : X ⟶ Y) (n : Nat) : (f.app _) '' (X.degenerate n) 
subseteq Y.degenerate n
参数：f : X ⟶ Y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `SSet.degenerate_le_preimage`：degenerate_le_preimage (f : X ⟶ Y) (n : Nat
) : X.degenerate n subseteq (f.app _) ⁻¹' (Y.degenerate n)
-/
lemma image_degenerate_le (f : X ⟶ Y) (n : ℕ) :
    (f.app _) '' (X.degenerate n) ⊆ Y.degenerate n := by
  simpa using degenerate_le_preimage f n
/-
**SSet.degenerate_iff_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : Nat} (x : X _⦋n⦌) : f.a
pp _ x in Y.degenerate n ↔ x in X.degenerate n
参数：f : X ⟶ Y；x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用引理 `SSet.degenerate_app_apply`：degenerate_app_apply {n : Nat} {x : X _⦋n⦌} (
hx : x in X.degenerate n) (f : X ⟶ Y) : f.app _ x in Y.degenerate n
-/
lemma degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : ℕ} (x : X _⦋n⦌) :
    f.app _ x ∈ Y.degenerate n ↔ x ∈ X.degenerate n := by
  constructor
  · intro hy
    simpa [← comp_apply, ← NatTrans.comp_app] using degenerate_app_apply hy (inv f)
  · exact fun hx ↦ degenerate_app_apply hx f
/-
**SSet.nonDegenerate_iff_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：nonDegenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : Nat} (x : X _⦋n⦌) : 
f.app _ x in Y.nonDegenerate n ↔ x in X.nonDegenerate n
参数：f : X ⟶ Y；x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonDegenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : ℕ} (x : X _⦋n⦌) :
    f.app _ x ∈ Y.nonDegenerate n ↔ x ∈ X.nonDegenerate n := by
  simp [mem_nonDegenerate_iff_notMem_degenerate,
    degenerate_iff_of_isIso]

attribute [local simp] nonDegenerate_iff_of_isIso in
/-- The bijection on nondegenerate simplices induced by an isomorphism
of simplicial sets. -/
@[simps]
/-
**SSet.nonDegenerateEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：nonDegenerateEquivOfIso (e : X ≅ Y) {n : Nat} : X.nonDegenerate n ≃ Y.nonD
egenerate n where toFun
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection on nondegenerate simplices induced by an isomorphism
of simplicial sets.
-/
def nonDegenerateEquivOfIso (e : X ≅ Y) {n : ℕ} :
    X.nonDegenerate n ≃ Y.nonDegenerate n where
  toFun := fun ⟨x, hx⟩ ↦ ⟨e.hom.app _ x, by aesop⟩
  invFun := fun ⟨y, hy⟩ ↦ ⟨e.inv.app _ y, by aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

end

set_option backward.isDefEq.respectTransparency false in
variable {X} in
/-
**SSet.degenerate_iff_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：degenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) : 
f.app _ x in Y.degenerate n ↔ x in X.degenerate n
参数：f : X ⟶ Y；x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.degenerate_iff_of_isIso`：degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso
 f] {n : Nat} (x : X _⦋n⦌) : f.app _ x in Y.degenerate n ↔ x in X.degenerate n
· 使用定理 `SSet.Subcomplex.instIsIsoToRangeOfMono`：∀ {X Y : _root_.SSet} (f : X ⟶ Y
) [CategoryTheory.Mono f], CategoryTheory.IsIso (SSet.Subcomplex.toRange f)
· 使用引理 `SSet.Subcomplex.mem_degenerate_iff`：mem_degenerate_iff {n : Nat} (x : A.
obj (op ⦋n⦌)) : dsimp% x in degenerate A n ↔ x.val in X.degenerate n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma degenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x ∈ Y.degenerate n ↔ x ∈ X.degenerate n := by
  rw [← degenerate_iff_of_isIso (Subcomplex.toRange f) x,
    Subcomplex.mem_degenerate_iff]
  simp

variable {X} in
/-
**SSet.nonDegenerate_iff_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：nonDegenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌)
 : f.app _ x in Y.nonDegenerate n ↔ x in X.nonDegenerate n
参数：f : X ⟶ Y；x : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonDegenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x ∈ Y.nonDegenerate n ↔ x ∈ X.nonDegenerate n := by
  simp [mem_nonDegenerate_iff_notMem_degenerate, degenerate_iff_of_mono]

end SSet

