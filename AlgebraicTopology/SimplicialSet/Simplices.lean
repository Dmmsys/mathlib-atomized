/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The preordered type of simplices of a simplicial set

In this file, we define the type `X.S` of simplices of a simplicial set `X`,
where a simplex consists of the data of `dim : ℕ` and `simplex : X _⦋dim⦌`.
We endow this type with a preorder defined by
`x ≤ y ↔ Subcomplex.ofSimplex x.simplex ≤ Subcomplex.ofSimplex y.simplex`.
In particular, as a preordered type, `X.S` is a category, but this is
not what is called "the category of simplices of `X`" in the literature
(and which is `X.Elementsᵒᵖ` in mathlib).

## TODO (@joelriou)

* Extend the `S` structure to define the type of nondegenerate
  simplices of a simplicial set `X`, and also the type of nondegenerate
  simplices of a simplicial set `X` which do not belong to a given subcomplex.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

/-- The type of simplices of a simplicial set `X`. This type `X.S` is in bijection
with `X.Elements` (see `SSet.S.equivElements`), but `X.S` is not what the literature
names "category of simplices of `X`", as the category on `X.S` comes from
a preorder (see `S.le_iff_nonempty_hom`). -/
/-
**SSet.S** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of simplices of a simplicial set `X`. This type `X.S` is in bijection
with `X.Elements` (see `SSet.S.equivElements`), but `X.S` is not what the litera
ture
names "category of simplices of `X`", as the category on `X.S` comes from
a preorder (see `S.le_iff_nonempty_hom`).
-/
structure S where
  /-- the dimension of the simplex -/
  {dim : ℕ}
  /-- the simplex -/
  simplex : X _⦋dim⦌

variable {X}

namespace S

/-
**SSet.S.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：mk_surjective (s : X.S) : exists (n : Nat) (x : X _⦋n⦌), s = mk x
参数：s : X.S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_surjective (s : X.S) :
    ∃ (n : ℕ) (x : X _⦋n⦌), s = mk x :=
  ⟨s.dim, s.simplex, rfl⟩

/-- The image of a simplex by a morphism of simplicial sets. -/
/-
**SSet.S.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：map {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) : Y.S
参数：f : X ⟶ Y；s : X.S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a simplex by a morphism of simplicial sets.
-/
def map {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) : Y.S :=
  S.mk (f.app _ s.simplex)
/-
**SSet.S.dim_eq_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：dim_eq_of_eq {s t : X.S} (h : s = t) : s.dim = t.dim
参数：h : s = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma dim_eq_of_eq {s t : X.S} (h : s = t) :
    s.dim = t.dim :=
  congr_arg dim h
/-
**SSet.S.dim_eq_of_mk_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：dim_eq_of_mk_eq {n m : Nat} {x : X _⦋n⦌} {y : X _⦋m⦌} (h : S.mk x = S.mk y
) : n = m
参数：h : S.mk x = S.mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.dim_eq_of_eq`：dim_eq_of_eq {s t : X.S} (h : s = t) : s.dim = t.di
m
-/
lemma dim_eq_of_mk_eq {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (h : S.mk x = S.mk y) : n = m :=
  dim_eq_of_eq h

section

variable (s : X.S) {d : ℕ} (hd : s.dim = d)

/-- When `s : X.S` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
@[simps dim]
/-
**SSet.S.cast** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：cast : X.S where dim
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `s : X.S` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`.
-/
def cast : X.S where
  dim := d
  simplex := _root_.cast (by simp only [hd]) s.simplex
/-
**SSet.S.cast_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：cast_eq_self : s.cast hd = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.mk_surjective`：mk_surjective (s : X.S) : exists (n : Nat) (x : X 
_⦋n⦌), s = mk x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma cast_eq_self : s.cast hd = s := by
  obtain ⟨d, _, rfl⟩ := s.mk_surjective
  obtain rfl := hd
  rfl

@[simp]
/-
**SSet.S.cast_simplex_rfl** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：cast_simplex_rfl : (s.cast rfl).simplex = s.simplex
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cast_simplex_rfl : (s.cast rfl).simplex = s.simplex := rfl

end

/-
**SSet.S.ext_iff'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：ext_iff' (s t : X.S) : s = t ↔ exists (h : s.dim = t.dim), (s.cast h).simp
lex = t.simplex
参数：s t : X.S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.mk_surjective`：mk_surjective (s : X.S) : exists (n : Nat) (x : X 
_⦋n⦌), s = mk x
· 使用定理 `SSet.S.mk.injEq`：∀ {X : _root_.SSet} {dim : ℕ} (simplex : X.obj (Opposit
e.op { len := dim })) (dim_1 : ℕ)   (simplex_1 : X.obj (Opposite.op { len := dim
_1 })…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext_iff' (s t : X.S) :
    s = t ↔ ∃ (h : s.dim = t.dim), (s.cast h).simplex = t.simplex :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ ↦ by
    obtain ⟨_, _, rfl⟩ := s.mk_surjective
    obtain ⟨_, _, rfl⟩ := t.mk_surjective
    aesop⟩
/-
**SSet.S.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：ext_iff {n : Nat} (x y : X _⦋n⦌) : S.mk x = S.mk y ↔ x = y
参数：x y : X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.S.mk.injEq`：∀ {X : _root_.SSet} {dim : ℕ} (simplex : X.obj (Opposit
e.op { len := dim })) (dim_1 : ℕ)   (simplex_1 : X.obj (Opposite.op { len := dim
_1 })…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ext_iff {n : ℕ} (x y : X _⦋n⦌) :
    S.mk x = S.mk y ↔ x = y := by
  simp

/-- The subcomplex generated by a simplex. -/
/-
**SSet.S.subcomplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.S`。
形式化陈述：subcomplex (s : X.S) : X.Subcomplex
参数：s : X.S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subcomplex generated by a simplex.
-/
abbrev subcomplex (s : X.S) : X.Subcomplex := Subcomplex.ofSimplex s.simplex
/-
**SSet.S.ofSimplex_eq_subcomplex_mk** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：ofSimplex_eq_subcomplex_mk {n : Nat} (x : X _⦋n⦌) : Subcomplex.ofSimplex x
 = (S.mk x).subcomplex
参数：x : X _⦋n⦌。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofSimplex_eq_subcomplex_mk {n : ℕ} (x : X _⦋n⦌) :
    Subcomplex.ofSimplex x = (S.mk x).subcomplex := rfl

@[simp]
/-
**SSet.S.subcomplex_cast** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：subcomplex_cast (s : X.S) {d : Nat} (hd : s.dim = d) : (s.cast hd).subcomp
lex = s.subcomplex
参数：s : X.S；hd : s.dim = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.cast_eq_self`：cast_eq_self : s.cast hd = s
-/
lemma subcomplex_cast (s : X.S) {d : ℕ} (hd : s.dim = d) :
    (s.cast hd).subcomplex = s.subcomplex := by
  rw [cast_eq_self]

/-- If `s : X.S` and `t : X.S` are simplices of a simplicial set, `s ≤ t` means
that the subcomplex generated by `s` is contained in the subcomplex generated by `t`,
see `SSet.S.le_def` and `SSet.S.le_iff`. Note that the
category structure on `X.S` induced by this preorder is not
the "category of simplices" of `X` (which is see `X.Elementsᵒᵖ`);
see `SSet.S.le_iff_nonempty_hom` for the precise relation. -/
/-
**SSet.S.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.S`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s : X.S` and `t : X.S` are simplices of a simplicial set, `s ≤ t` means
that the subcomplex generated by `s` is contained in the subcomplex generated by
 `t`,
see `SSet.S.le_def` and `SSet.S.le_iff`. Note that the
category structure on `X.S` induced by this preorder is not
the "category of simplices" of `X` (which is see `X.Elementsᵒᵖ`);
see `SSet.S.le_iff_nonempty_hom` for the precise relation.
-/
instance : Preorder X.S := Preorder.lift subcomplex
/-
**SSet.S.le_def** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：le_def {s t : X.S} : s <= t ↔ s.subcomplex <= t.subcomplex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def {s t : X.S} : s ≤ t ↔ s.subcomplex ≤ t.subcomplex :=
  Iff.rfl
/-
**SSet.S.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：le_iff {s t : X.S} : s <= t ↔ exists (f : ⦋s.dim⦌ ⟶ ⦋t.dim⦌), X.map f.op t
.simplex = s.simplex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.le_def`：le_def {s t : X.S} : s <= t ↔ s.subcomplex <= t.subcomple
x
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用定理 `CategoryTheory.Subfunctor.ofSection_obj`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : Cᵒᵖ}   
(x : F.obj X) (U : Cᵒᵖ),   (C…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
-/
lemma le_iff {s t : X.S} :
    s ≤ t ↔ ∃ (f : ⦋s.dim⦌ ⟶ ⦋t.dim⦌), X.map f.op t.simplex = s.simplex := by
  rw [le_def, Subcomplex.ofSimplex_le_iff, Subfunctor.ofSection_obj, Set.mem_ofPred_eq]
  tauto
/-
**SSet.S.mk_map_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：mk_map_le {n m : Nat} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) : S.mk (X.map f.op x) <
= S.mk x
参数：x : X _⦋n⦌；f : ⦋m⦌ ⟶ ⦋n⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.le_iff`：le_iff {s t : X.S} : s <= t ↔ exists (f : ⦋s.dim⦌ ⟶ ⦋t.di
m⦌), X.map f.op t.simplex = s.simplex
-/
lemma mk_map_le {n m : ℕ} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    S.mk (X.map f.op x) ≤ S.mk x := by
  rw [le_iff]
  tauto
/-
**SSet.S.mk_map_eq_iff_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：mk_map_eq_iff_of_mono {n m : Nat} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] : 
S.mk (X.map f.op x) = S.mk x ↔ IsIso f
参数：x : X _⦋n⦌；f : ⦋m⦌ ⟶ ⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimplexCategory.eq_id_of_mono`：eq_id_of_mono {x : SimplexCategory} (i : 
x ⟶ x) [Mono i] : i = 𝟙 _
· 使用引理 `SSet.S.dim_eq_of_mk_eq`：dim_eq_of_mk_eq {n m : Nat} {x : X _⦋n⦌} {y : X 
_⦋m⦌} (h : S.mk x = S.mk y) : n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimplexCategory.eq_id_of_isIso`：eq_id_of_isIso {x : SimplexCategory} (f 
: x ⟶ x) [IsIso f] : f = 𝟙 _
· 使用引理 `SimplexCategory.eq_of_isIso`：eq_of_isIso {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Is
Iso f] : n = m
-/
lemma mk_map_eq_iff_of_mono {n m : ℕ} (x : X _⦋n⦌)
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] :
    S.mk (X.map f.op x) = S.mk x ↔ IsIso f := by
  constructor
  · intro h
    obtain rfl := S.dim_eq_of_mk_eq h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    infer_instance
  · intro hf
    obtain rfl := SimplexCategory.eq_of_isIso f
    obtain rfl := SimplexCategory.eq_id_of_isIso f
    simp

/-- The type of simplices of `X : SSet.{u}` identifies to the type
of elements of `X` considered as a functor `SimplexCategoryᵒᵖ ⥤ Type u`.
(Note that this is not an (anti)equivalence of categories,
see `S.le_iff_nonempty_hom`.) -/
@[simps!]
/-
**SSet.S.equivElements** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：equivElements : X.S ≃ X.Elements where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of simplices of `X : SSet.{u}` identifies to the type
of elements of `X` considered as a functor `SimplexCategoryᵒᵖ ⥤ Type u`.
(Note that this is not an (anti)equivalence of categories,
see `S.le_iff_nonempty_hom`.)
-/
def equivElements : X.S ≃ X.Elements where
  toFun s := X.elementsMk _ s.simplex
  invFun := by rintro ⟨⟨⟨n⟩⟩, x⟩; exact S.mk x
  left_inv _ := rfl
  right_inv _ := rfl
/-
**SSet.S.le_iff_nonempty_hom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S`。
形式化陈述：le_iff_nonempty_hom (x y : X.S) : x <= y ↔ Nonempty (equivElements y ⟶ equ
ivElements x)
参数：x y : X.S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.le_iff`：le_iff {s t : X.S} : s <= t ↔ exists (f : ⦋s.dim⦌ ⟶ ⦋t.di
m⦌), X.map f.op t.simplex = s.simplex
-/
lemma le_iff_nonempty_hom (x y : X.S) :
    x ≤ y ↔ Nonempty (equivElements y ⟶ equivElements x) := by
  rw [le_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f.op, hf⟩⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.unop, hf⟩

/-- The bijection `X.op.S ≃ X.S`. -/
@[simps -isSimp apply symm_apply]
/-
**SSet.S.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：opEquiv : X.op.S ≃ X.S where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `X.op.S ≃ X.S`.
-/
def opEquiv : X.op.S ≃ X.S where
  toFun x := S.mk (opObjEquiv x.simplex)
  invFun y := S.mk (opObjEquiv.symm y.simplex)

/-- The bijection `X.S ≃ Y.S` on simplices of simplicial sets that
is induced by an isomorphism `X ≅ Y`. -/
@[simps -isSimp apply symm_apply]
/-
**SSet.S.equivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：equivOfIso {Y : SSet.{u}} (e : X ≅ Y) : X.S ≃ Y.S where toFun s
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `X.S ≃ Y.S` on simplices of simplicial sets that
is induced by an isomorphism `X ≅ Y`.
-/
def equivOfIso {Y : SSet.{u}} (e : X ≅ Y) : X.S ≃ Y.S where
  toFun s := S.mk (e.hom.app _ s.simplex)
  invFun s := S.mk (e.inv.app _ s.simplex)
  left_inv _ := by simp
  right_inv _ := by simp

end S

end SSet

