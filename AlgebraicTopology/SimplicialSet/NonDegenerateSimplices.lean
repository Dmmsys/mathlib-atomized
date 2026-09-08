/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
# The partially ordered type of non degenerate simplices of a simplicial set

In this file, we introduce the partially ordered type `X.N` of
non degenerate simplices of a simplicial set `X`. We obtain
an embedding `X.orderEmbeddingN : X.N ↪o X.Subcomplex` which sends
a non degenerate simplex to the subcomplex of `X` it generates.

Given an arbitrary simplex `x : X.S`, we show that there is a unique
non degenerate `x.toN : X.N` such that `x.toN.subcomplex = x.subcomplex`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

/-- The type of non degenerate simplices of a simplicial set. -/
/-
**SSet.N** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of non degenerate simplices of a simplicial set.
-/
structure N extends X.S where mk' ::
  nonDegenerate : simplex ∈ X.nonDegenerate _

namespace N

variable {X}

/-
**SSet.N.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SSet.N`。
形式化陈述：∀ {X : _root_.SSet} (s : X.N), ∃ t, ∃ (ht : t.simplex ∈ X.nonDegenerate t.
dim), s = { toS := t, nonDegenerate := ht }
参数：s : X.N；ht : t.simplex ∈ X.nonDegenerate t.dim。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.N.mk'`：mk'_surjective (s : X.N) : exists (t : X.S) (ht : t.simplex 
in X.nonDegenerate _), s = mk' t ht
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
-/
lemma mk'_surjective (s : X.N) :
    ∃ (t : X.S) (ht : t.simplex ∈ X.nonDegenerate _), s = mk' t ht :=
  ⟨s.toS, s.nonDegenerate, rfl⟩

/-- Constructor for the type of non degenerate simplices of a simplicial set. -/
@[simps]
/-
**SSet.N.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.N`。
形式化陈述：mk {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) : X.N where simple
x
参数：x : X _⦋n⦌；hx : x in X.nonDegenerate n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.N.mk'`：mk'_surjective (s : X.N) : exists (t : X.S) (ht : t.simplex 
in X.nonDegenerate _), s = mk' t ht

--- 原说明 ---
Constructor for the type of non degenerate simplices of a simplicial set.
-/
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) : X.N where
  simplex := x
  nonDegenerate := hx
/-
**SSet.N.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：mk_surjective (x : X.N) : exists (n : Nat) (y : X.nonDegenerate n), x = N.
mk _ y.prop
参数：x : X.N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
-/
lemma mk_surjective (x : X.N) :
    ∃ (n : ℕ) (y : X.nonDegenerate n), x = N.mk _ y.prop :=
  ⟨x.dim, ⟨_, x.nonDegenerate⟩, rfl⟩

/-- Induction principle for the type `X.N` of nondegenerate simplices of
a simplicial set `X`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**SSet.N.induction** 是 Mathlib 中的一个定义，位于命名空间 `SSet.N`。
形式化陈述：induction {motive : X.N -> Sort*} (mk : forall (n : Nat) (x : X.nonDegener
ate n), motive (mk x.val x.property)) (s : X.N) : motive s
参数：mk : forall (n : Nat) (x : X.nonDegenerate n), motive (mk x.val x.property)；s
 : X.N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim

--- 原说明 ---
Induction principle for the type `X.N` of nondegenerate simplices of
a simplicial set `X`.
-/
def induction {motive : X.N → Sort*}
    (mk : ∀ (n : ℕ) (x : X.nonDegenerate n), motive (mk x.val x.property)) (s : X.N) :
    motive s :=
  mk s.dim ⟨_, s.nonDegenerate⟩

@[simp]
/-
**SSet.N.induction_mk** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：induction_mk {motive : X.N -> Sort*} (mk : forall (n : Nat) (x : X.nonDege
nerate n), motive (mk x.1 x.2)) {n : Nat} (s : X.nonDegenerate n) : induction (m
otive
参数：mk : forall (n : Nat) (x : X.nonDegenerate n), motive (mk x.1 x.2)；s : X.nonD
egenerate n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma induction_mk {motive : X.N → Sort*}
    (mk : ∀ (n : ℕ) (x : X.nonDegenerate n), motive (mk x.1 x.2)) {n : ℕ} (s : X.nonDegenerate n) :
  induction (motive := motive) mk (N.mk s.val s.property) = mk n s := rfl
/-
**SSet.N.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：ext_iff (x y : X.N) : x = y ↔ x.toS = y.toS
参数：x y : X.N。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ext_iff (x y : X.N) :
    x = y ↔ x.toS = y.toS := by
  grind [cases SSet.N]
/-
**SSet.N.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.N`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder X.N := Preorder.lift toS
/-
**SSet.N.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：le_iff {x y : X.N} : x <= y ↔ x.subcomplex <= y.subcomplex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff {x y : X.N} : x ≤ y ↔ x.subcomplex ≤ y.subcomplex :=
  Iff.rfl
/-
**SSet.N.lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：lt_iff {x y : X.N} : x < y ↔ x.subcomplex < y.subcomplex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_iff {x y : X.N} : x < y ↔ x.subcomplex < y.subcomplex :=
  Iff.rfl
/-
**SSet.N.le_iff_exists_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：le_iff_exists_mono {x y : X.N} : x <= y ↔ exists (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (
_ : Mono f), X.map f.op y.simplex = x.simplex
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
· 使用引理 `SSet.mono_of_nonDegenerate`：mono_of_nonDegenerate (x : X.nonDegenerate n
) {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) (y : X.obj (op m)) (hy : X.map f.op y = x)
 : Mono f
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
-/
lemma le_iff_exists_mono {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex := by
  simp only [le_iff, CategoryTheory.Subfunctor.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨f, X.mono_of_nonDegenerate ⟨_, x.nonDegenerate⟩ f _ hf, hf⟩, by tauto⟩
/-
**SSet.N.dim_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：dim_le_of_le {x y : X.N} (h : x <= y) : x.dim <= y.dim
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.N.le_iff_exists_mono`：le_iff_exists_mono {x y : X.N} : x <= y ↔ exi
sts (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex
· 使用定理 `SimplexCategory.len_le_of_mono`：len_le_of_mono {x y : SimplexCategory} (
f : x ⟶ y) [Mono f] : x.len <= y.len
-/
lemma dim_le_of_le {x y : X.N} (h : x ≤ y) : x.dim ≤ y.dim := by
  rw [le_iff_exists_mono] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.N.dim_lt_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：dim_lt_of_lt {x y : X.N} (h : x < y) : x.dim < y.dim
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用引理 `SSet.N.dim_le_of_le`：dim_le_of_le {x y : X.N} (h : x <= y) : x.dim <= y.
dim
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SSet.N.le_iff_exists_mono`：le_iff_exists_mono {x y : X.N} : x <= y ↔ exi
sts (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `SSet.N.mk_surjective`：mk_surjective (x : X.N) : exists (n : Nat) (y : X.
nonDegenerate n), x = N.mk _ y.prop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimplexCategory.eq_id_of_mono`：eq_id_of_mono {x : SimplexCategory} (i : 
x ⟶ x) [Mono i] : i = 𝟙 _
-/
lemma dim_lt_of_lt {x y : X.N} (h : x < y) : x.dim < y.dim := by
  obtain h' | h' := (dim_le_of_le h.le).lt_or_eq
  · exact h'
  · obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h.le
    obtain ⟨d, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
    obtain ⟨d', ⟨y, hy⟩, rfl⟩ := y.mk_surjective
    obtain rfl : d = d' := h'
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obtain rfl : y = x := by simpa using hf
    simp at h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.N.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.N`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder X.N where
  le_antisymm x₁ x₂ h h' := by
    obtain ⟨n₁, ⟨x₁, hx₁⟩, rfl⟩ := x₁.mk_surjective
    obtain ⟨n₂, ⟨x₂, hx₂⟩, rfl⟩ := x₂.mk_surjective
    obtain rfl : n₁ = n₂ := le_antisymm (dim_le_of_le h) (dim_le_of_le h')
    rw [le_iff_exists_mono] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aesop
/-
**SSet.N.subcomplex_injective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：subcomplex_injective {x y : X.N} (h : x.subcomplex = y.subcomplex) : x = y
参数：h : x.subcomplex = y.subcomplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.N.le_iff`：le_iff {x y : X.N} : x <= y ↔ x.subcomplex <= y.subcomple
x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma subcomplex_injective {x y : X.N} (h : x.subcomplex = y.subcomplex) :
    x = y := by
  apply le_antisymm
  all_goals
  · rw [le_iff, h]
/-
**SSet.N.subcomplex_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：subcomplex_injective_iff {x y : X.N} : x.subcomplex = y.subcomplex ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.N.subcomplex_injective`：subcomplex_injective {x y : X.N} (h : x.sub
complex = y.subcomplex) : x = y
-/
lemma subcomplex_injective_iff {x y : X.N} :
    x.subcomplex = y.subcomplex ↔ x = y :=
  ⟨subcomplex_injective, by rintro rfl; rfl⟩
/-
**SSet.N.eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：eq_iff {x y : X.N} : x = y ↔ x.subcomplex = y.subcomplex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma eq_iff {x y : X.N} :
    x = y ↔ x.subcomplex = y.subcomplex :=
  ⟨by rintro rfl; rfl, fun h ↦ by simp [le_antisymm_iff, le_iff, h]⟩

section

variable (s : X.N) {d : ℕ} (hd : s.dim = d)

/-- When `s : X.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
/-
**SSet.N.cast** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.N`。
形式化陈述：cast : X.N where toS
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.N.mk'`：mk'_surjective (s : X.N) : exists (t : X.S) (ht : t.simplex 
in X.nonDegenerate _), s = mk' t ht

--- 原说明 ---
When `s : X.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`.
-/
abbrev cast : X.N where
  toS := s.toS.cast hd
  nonDegenerate := by
    subst hd
    exact s.nonDegenerate
/-
**SSet.N.cast_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：cast_eq_self : s.cast hd = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

variable (X) in
/-
**SSet.N.iSup_subcomplex_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：iSup_subcomplex_eq_top : ⨆ (s : X.N), s.subcomplex = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top`：iSup_ofSimplex_nonD
egenerate_eq_top : ⨆ (x : Σ (p : Nat), X.nonDegenerate p), ofSimplex x.2.val = ⊤
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iSup_subcomplex_eq_top :
    ⨆ (s : X.N), s.subcomplex = ⊤ :=
  le_antisymm (by simp) (by
    rw [← Subcomplex.iSup_ofSimplex_nonDegenerate_eq_top X, iSup_le_iff]
    rintro ⟨d, s, hs⟩
    exact le_trans (by rfl) (le_iSup _ (N.mk _ hs)))
/-
**SSet.N.subcomplex_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：subcomplex_le_iff {A B : X.Subcomplex} : A <= B ↔ forall (s : X.N), s.subc
omplex <= A -> s.subcomplex <= B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.le_iff_contains_nonDegenerate`：le_iff_contains_nonDegene
rate (B : X.Subcomplex) : A <= B ↔ forall (n : Nat) (x : X.nonDegenerate n), x.v
al in A.obj _ -> x.val in B.obj _
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SSet.N.mk_simplex`：∀ {X : _root_.SSet} {n : ℕ} (x : X.obj (Opposite.op {
 len := n })) (hx : x ∈ X.nonDegenerate n),   (SSet.N.mk x hx).simplex = x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma subcomplex_le_iff {A B : X.Subcomplex} :
    A ≤ B ↔ ∀ (s : X.N), s.subcomplex ≤ A → s.subcomplex ≤ B := by
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  refine ⟨fun h s ↦ ?_, fun h n x hx ↦ ?_⟩
  · induction s using N.induction with
    | mk n x =>
      intro hx
      simp only [Subfunctor.ofSection_le_iff, mk_simplex] at hx ⊢
      exact h _ _ hx
  · simpa using! h (N.mk _ x.prop) (by simpa)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `X.op.N ≃ X.N`. -/
@[simps -isSimp apply symm_apply]
/-
**SSet.N.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.N`。
形式化陈述：opEquiv : X.op.N ≃o X.N where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `X.op.N ≃ X.N`.
-/
def opEquiv : X.op.N ≃o X.N where
  toFun x := N.mk (opObjEquiv x.simplex)
    (by simpa only [opObjEquiv_mem_nonDegenerate_iff] using x.nonDegenerate)
  invFun y := N.mk (opObjEquiv.symm y.simplex)
    (by simpa [← opObjEquiv_mem_nonDegenerate_iff] using y.nonDegenerate)
  map_rel_iff' {x y} := by
    dsimp
    simp only [le_iff, Subcomplex.ofSimplex_le_iff, Subcomplex.mem_ofSimplex_obj_iff]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨SimplexCategory.rev.map f, by simp [op_map, dsimp% hf]⟩
    · rintro ⟨f, hf⟩
      exact ⟨SimplexCategory.rev.map f, by simp [op_map, ← hf]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `X.N ≃ Y.N` on nondegenerate simplices of simplicial sets
that is induced by an isomorphism `X ≅ Y`. -/
@[simps -isSimp apply symm_apply]
/-
**SSet.N.orderIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.N`。
形式化陈述：orderIsoOfIso {Y : SSet.{u}} (e : X ≅ Y) : X.N ≃o Y.N where toFun x
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `X.N ≃ Y.N` on nondegenerate simplices of simplicial sets
that is induced by an isomorphism `X ≅ Y`.
-/
def orderIsoOfIso {Y : SSet.{u}} (e : X ≅ Y) : X.N ≃o Y.N where
  toFun x := N.mk (e.hom.app _ x.simplex)
    ((nonDegenerate_iff_of_isIso e.hom x.simplex).mpr x.nonDegenerate)
  invFun y := N.mk (e.inv.app _ y.simplex)
    ((nonDegenerate_iff_of_isIso e.inv y.simplex).mpr y.nonDegenerate)
  left_inv x := by simp [N.ext_iff, S.ext_iff']
  right_inv _ := by simp [N.ext_iff, S.ext_iff']
  map_rel_iff' {x y} := by
    dsimp
    simp only [le_iff, Subcomplex.ofSimplex_le_iff, Subcomplex.mem_ofSimplex_obj_iff]
    refine exists_congr (fun f ↦ ?_)
    dsimp at f ⊢
    rw [← NatTrans.naturality_apply e.hom f.op]
    exact (e.app _).toEquiv.apply_eq_iff_eq

end N

/-- The map which sends a non degenerate simplex of a simplicial set to
the subcomplex it generates is an order embedding. -/
@[simps]
/-
**SSet.orderEmbeddingN** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：orderEmbeddingN : X.N ↪o X.Subcomplex where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map which sends a non degenerate simplex of a simplicial set to
the subcomplex it generates is an order embedding.
-/
def orderEmbeddingN : X.N ↪o X.Subcomplex where
  toFun x := x.subcomplex
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

namespace S

variable {X}

/-
**SSet.S.eq_iff_ofSimplex_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：eq_iff_ofSimplex_eq {X : SSet.{u}} {n m : Nat} (x : X _⦋n⦌) (y : X _⦋m⦌) (
hx : x in X.nonDegenerate _) (hy : y in X.nonDegenerate _) : S.mk x = S.mk y ↔ S
ubcomplex.ofSimplex x = Subcomplex.ofSimplex y
参数：x : X _⦋n⦌；y : X _⦋m⦌；hx : x in X.nonDegenerate _；hy : y in X.nonDegenerate _
。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `SSet.N.ext_iff`：ext_iff (x y : X.N) : x = y ↔ x.toS = y.toS
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_iff_ofSimplex_eq {X : SSet.{u}} {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (hx : x ∈ X.nonDegenerate _) (hy : y ∈ X.nonDegenerate _) :
    S.mk x = S.mk y ↔ Subcomplex.ofSimplex x = Subcomplex.ofSimplex y := by
  trans N.mk x hx = N.mk y hy
  · exact (N.ext_iff (N.mk x hx) (N.mk y hy)).symm
  · simp only [le_antisymm_iff]
    rfl
/-
**SSet.S.subcomplex_map_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：subcomplex_map_le (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (hf : X.map f.op y.s
implex = x.simplex) : x.subcomplex <= y.subcomplex
参数：x y : X.S；f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌；hf : X.map f.op y.simplex = x.simplex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subcomplex_map_le (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌)
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex ≤ y.subcomplex := by
  simp only [Subcomplex.ofSimplex_le_iff]
  exact ⟨_, hf⟩
/-
**SSet.S.subcomplex_eq_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：subcomplex_eq_of_epi (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f] (hf : X.m
ap f.op y.simplex = x.simplex) : x.subcomplex = y.subcomplex
参数：x y : X.S；f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌；hf : X.map f.op y.simplex = x.simplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SSet.S.subcomplex_map_le`：subcomplex_map_le (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋
y.dim⦌) (hf : X.map f.op y.simplex = x.simplex) : x.subcomplex <= y.subcomplex
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
lemma subcomplex_eq_of_epi (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f]
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex = y.subcomplex := by
  refine le_antisymm (subcomplex_map_le x y f hf) ?_
  simp only [Subcomplex.ofSimplex_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← hf, ← Functor.map_comp_apply, ← op_comp]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.S.existsUnique_n** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：existsUnique_n (x : X.S) : exists! (y : X.N), y.subcomplex = x.subcomplex
参数：x : X.S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用引理 `SSet.S.mk_surjective`：mk_surjective (s : X.S) : exists (n : Nat) (x : X 
_⦋n⦌), s = mk x
· 使用引理 `SSet.exists_nonDegenerate`：exists_nonDegenerate (x : X _⦋n⦌) : exists (m
 : Nat) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f) (y : X.nonDegenerate m), x = X.map f.op y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.isSplitEpi_of_epi`：isSplitEpi_of_epi [SplitEpiCategory C]
 {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f
· 使用定理 `SimplexCategory.instSplitEpiCategory`：CategoryTheory.SplitEpiCategory Si
mplexCategory
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.instIsSplitMonoMap`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {X Y : C} (f : Y ⟶…
· 使用定理 `CategoryTheory.instIsSplitMonoOppositeOpOfIsSplitMono`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} [CategoryTheory
.IsSplitEpi f],   CategoryTheory.IsSplitMon…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `SSet.N.subcomplex_injective`：subcomplex_injective {x y : X.N} (h : x.sub
complex = y.subcomplex) : x = y
-/
lemma existsUnique_n (x : X.S) : ∃! (y : X.N), y.subcomplex = x.subcomplex :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
    obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
    refine ⟨N.mk _ y.prop, le_antisymm ?_ ?_⟩
    · simp only [Subcomplex.ofSimplex_le_iff]
      have := isSplitEpi_of_epi f
      have : Function.Injective (X.map f.op) := by
        rw [← mono_iff_injective]
        infer_instance
      refine ⟨(section_ f).op, this ?_⟩
      dsimp
      rw [← comp_apply, ← Functor.map_comp, ← comp_apply, ← Functor.map_comp,
        ← op_comp, ← op_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]
    · simp only [Subcomplex.ofSimplex_le_iff]
      exact ⟨f.op, rfl⟩)
    (fun y₁ y₂ h₁ h₂ ↦ N.subcomplex_injective (by rw [h₁, h₂]))

/-- This is the non degenerate simplex of a simplicial set which
generates the same subcomplex as a given simplex. -/
/-
**SSet.S.toN** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：toN (x : X.S) : X.N
参数：x : X.S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the non degenerate simplex of a simplicial set which
generates the same subcomplex as a given simplex.
-/
noncomputable def toN (x : X.S) : X.N := x.existsUnique_n.exists.choose

@[simp]
/-
**SSet.S.subcomplex_toN** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：subcomplex_toN (x : X.S) : x.toN.subcomplex = x.subcomplex
参数：x : X.S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用引理 `SSet.S.existsUnique_n`：existsUnique_n (x : X.S) : exists! (y : X.N), y.s
ubcomplex = x.subcomplex
-/
lemma subcomplex_toN (x : X.S) : x.toN.subcomplex = x.subcomplex :=
  x.existsUnique_n.exists.choose_spec
/-
**SSet.S.toN_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：toN_eq_iff {x : X.S} {y : X.N} : x.toN = y ↔ y.subcomplex = x.subcomplex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.subcomplex_toN`：subcomplex_toN (x : X.S) : x.toN.subcomplex = x.s
ubcomplex
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用引理 `SSet.S.existsUnique_n`：existsUnique_n (x : X.S) : exists! (y : X.N), y.s
ubcomplex = x.subcomplex
-/
lemma toN_eq_iff {x : X.S} {y : X.N} :
    x.toN = y ↔ y.subcomplex = x.subcomplex :=
  ⟨by rintro rfl; simp, fun h ↦ x.existsUnique_n.unique (by simp) h⟩

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.S.existsUnique_toN** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma existsUnique_toNπ {x : X.S} {y : X.N} (hy : x.toN = y) :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Epi f ∧ X.map f.op y.simplex = x.simplex := by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff, hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  refine existsUnique_of_exists_of_unique ⟨f, inferInstance, rfl⟩
    (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ ↦ unique_nonDegenerate_map _ _ _ _ hf₁.symm _ _ hf₂.symm)

/-- Given a simplex `x : X.S` of a simplicial set `X`, this is the unique
(epi)morphism `f : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌` such that `x.simplex` is
`X.map f.op x.toN.simplex` where `x.toN : X.N` is the unique nondegenerate
simplex of `X` which generates the same subcomplex as `x`. -/
/-
**SSet.S.toN** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：toN (x : X.S) : X.N
参数：x : X.S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a simplex `x : X.S` of a simplicial set `X`, this is the unique
(epi)morphism `f : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌` such that `x.simplex` is
`X.map f.op x.toN.simplex` where `x.toN : X.N` is the unique nondegenerate
simplex of `X` which generates the same subcomplex as `x`.
-/
@[no_expose] noncomputable def toNπ (x : X.S) : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌ :=
  (existsUnique_toNπ rfl).exists.choose
/-
**SSet.S.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.S`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X.S) : Epi x.toNπ := (existsUnique_toNπ rfl).exists.choose_spec.1

@[simp]
/-
**SSet.S.map_toN** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_toNπ_op_apply (x : X.S) :
    X.map x.toNπ.op x.toN.simplex = x.simplex := (existsUnique_toNπ rfl).exists.choose_spec.2
/-
**SSet.S.dim_toN_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：dim_toN_le (x : X.S) : x.toN.dim <= x.dim
参数：x : X.S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.le_of_epi`：le_of_epi {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
 : m <= n
· 使用定理 `SSet.S.instEpiSimplexCategoryToNπ`：∀ {X : _root_.SSet} (x : X.S), Catego
ryTheory.Epi x.toNπ
-/
lemma dim_toN_le (x : X.S) :
    x.toN.dim ≤ x.dim :=
  SimplexCategory.le_of_epi x.toNπ

end S

end SSet

