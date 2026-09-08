/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices

/-!
# Simplices that are uniquely codimensional one faces

Let `X` be a simplicial set. If `x : X _⦋d⦌` and `y : X _⦋d + 1⦌`,
we say that `x` is uniquely a `1`-codimensional face of `y` if there
exists a unique `i : Fin (d + 2)` such that `X.δ i y = x`. In this file,
we extend this to a predicate `IsUniquelyCodimOneFace` involving two terms
in the type `X.S` of simplices of `X`. This is used in the
file `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean` for the
study of strong (inner) anodyne extensions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.S

variable {X : SSet.{u}} (x y : X.S)

/-- The property that a simplex is uniquely a `1`-codimensional face of another simplex -/
/-
**SSet.S.IsUniquelyCodimOneFace** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S`。
形式化陈述：IsUniquelyCodimOneFace : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a simplex is uniquely a `1`-codimensional face of another simp
lex
-/
def IsUniquelyCodimOneFace : Prop :=
  y.dim = x.dim + 1 ∧ ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.simplex = x.simplex

namespace IsUniquelyCodimOneFace

/-
**SSet.S.IsUniquelyCodimOneFace.iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniquely
CodimOneFace`。
形式化陈述：iff {d : Nat} (x : X _⦋d⦌) (y : X _⦋d + 1⦌) : IsUniquelyCodimOneFace (S.mk
 x) (S.mk y) ↔ exists! (i : Fin (d + 2)), X.δ i y = x
参数：x : X _⦋d⦌；y : X _⦋d + 1⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.eq_δ_of_mono`：eq_δ_of_mono {n : Nat} (θ : ⦋n⦌ ⟶ ⦋n + 1⦌)
 [Mono θ] : exists i : Fin (n + 2), θ = δ i
· 使用引理 `SimplexCategory.δ_injective`：δ_injective {n : Nat} : Function.Injective 
(δ (n
· 使用定理 `SimplexCategory.instMonoδ`：∀ {n : ℕ} {i : Fin (n + 2)}, CategoryTheory.M
ono (SimplexCategory.δ i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma iff {d : ℕ} (x : X _⦋d⦌) (y : X _⦋d + 1⦌) :
    IsUniquelyCodimOneFace (S.mk x) (S.mk y) ↔
      ∃! (i : Fin (d + 2)), X.δ i y = x := by
  constructor
  · rintro ⟨_, ⟨f, ⟨_, h₁⟩, h₂⟩⟩
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    exact ⟨i, h₁, fun j hj ↦ SimplexCategory.δ_injective (h₂ _ ⟨inferInstance, hj⟩)⟩
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ ↦ ?_⟩
    obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl : j = i := h₂ _ h₄
    rfl

variable {x y} (hxy : IsUniquelyCodimOneFace x y)

include hxy in
/-
**SSet.S.IsUniquelyCodimOneFace.dim_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniqu
elyCodimOneFace`。
形式化陈述：dim_eq : y.dim = x.dim + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma dim_eq : y.dim = x.dim + 1 := hxy.1

section

variable {d : ℕ} (hd : x.dim = d)

/-
**SSet.S.IsUniquelyCodimOneFace.cast** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniquel
yCodimOneFace`。
形式化陈述：cast : IsUniquelyCodimOneFace (x.cast hd) (y.cast (d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.cast_eq_self`：cast_eq_self : s.cast hd = s
-/
lemma cast : IsUniquelyCodimOneFace (x.cast hd) (y.cast (d := d + 1) (by rw [hxy.dim_eq, hd])) := by
  simpa only [cast_eq_self]
/-
**SSet.S.IsUniquelyCodimOneFace.existsUnique_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.
IsUniquelyCodimOneFace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma existsUnique_δ_cast_simplex :
    ∃! (i : Fin (d + 2)), X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex =
      (x.cast hd).simplex := by
  simpa only [S.cast, iff] using hxy.cast hd

include hxy in
/-- When a `d`-dimensional simplex `x` is a `1`-codimensional face of `y`, this is
the only `i : Fin (d + 2)`, such that `X.δ i y = x` (with an abuse of notation:
see `δ_index` and `δ_eq_iff` for well typed statements). -/
/-
**SSet.S.IsUniquelyCodimOneFace.index** 是 Mathlib 中的一个定义，位于命名空间 `SSet.S.IsUnique
lyCodimOneFace`。
形式化陈述：index : Fin (d + 2)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a `d`-dimensional simplex `x` is a `1`-codimensional face of `y`, this is
the only `i : Fin (d + 2)`, such that `X.δ i y = x` (with an abuse of notation:
see `δ_index` and `δ_eq_iff` for well typed statements).
-/
noncomputable def index : Fin (d + 2) :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose
/-
**SSet.S.IsUniquelyCodimOneFace.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniquelyCod
imOneFace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_index :
    X.δ (hxy.index hd) (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose_spec
/-
**SSet.S.IsUniquelyCodimOneFace.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniquelyCod
imOneFace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq_iff (i : Fin (d + 2)) :
    X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔
      i = hxy.index hd :=
  ⟨fun h ↦ (hxy.existsUnique_δ_cast_simplex hd).unique h (hxy.δ_index hd),
    by rintro rfl; apply δ_index⟩

include hxy in
/-
**SSet.S.IsUniquelyCodimOneFace.le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniquelyC
odimOneFace`。
形式化陈述：le : x <= y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_index`：δ_index : X.δ (hxy.index hd) (y.c
ast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.le_def`：le_def {s t : X.S} : s <= t ↔ s.subcomplex <= t.subcomple
x
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.dim_eq`：dim_eq : y.dim = x.dim + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.S.subcomplex_cast`：subcomplex_cast (s : X.S) {d : Nat} (hd : s.dim 
= d) : (s.cast hd).subcomplex = s.subcomplex
· 使用引理 `CategoryTheory.Subfunctor.ofSection_le_iff`：ofSection_le_iff (G : Subfun
ctor F) : ofSection x <= G ↔ x in G.obj X
-/
lemma le : x ≤ y := by
  have := hxy.δ_index rfl
  simp only [cast_simplex_rfl] at this
  rw [S.le_def, ← y.subcomplex_cast hxy.dim_eq, Subfunctor.ofSection_le_iff,
    ← this]
  exact ⟨(SimplexCategory.δ _).op, rfl⟩

set_option backward.defeqAttrib.useBackward true in
include hxy in
/-
**SSet.S.IsUniquelyCodimOneFace.unique** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniqu
elyCodimOneFace`。
形式化陈述：unique (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f] (hf : X.map f.op (y.cast (by rw [hxy.d
im_eq, hd])).simplex = (x.cast hd).simplex) : f = SimplexCategory.δ (hxy.index h
d)
参数：f : ⦋d⦌ ⟶ ⦋d + 1⦌；hf : X.map f.op (y.cast (by rw [hxy.dim_eq, hd])).simplex =
 (x.cast hd).simplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.cast`：cast : IsUniquelyCodimOneFace (x.cas
t hd) (y.cast (d
· 使用定理 `SimplexCategory.instMonoδ`：∀ {n : ℕ} {i : Fin (n + 2)}, CategoryTheory.M
ono (SimplexCategory.δ i)
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_index`：δ_index : X.δ (hxy.index hd) (y.c
ast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex
-/
lemma unique (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f]
    (hf : X.map f.op (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex) :
    f = SimplexCategory.δ (hxy.index hd) :=
  (hxy.cast hd).2.unique ⟨by dsimp; infer_instance, hf⟩
    ⟨by dsimp; infer_instance, hxy.δ_index hd⟩

end

set_option backward.isDefEq.respectTransparency.types false in
include hxy in
/-
**SSet.S.IsUniquelyCodimOneFace.op** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniquelyC
odimOneFace`。
形式化陈述：op : (S.opEquiv.symm x).IsUniquelyCodimOneFace (S.opEquiv.symm y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `SSet.S.mk_surjective`：mk_surjective (s : X.S) : exists (n : Nat) (x : X 
_⦋n⦌), s = mk x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.S.opEquiv_symm_apply`：∀ {X : _root_.SSet} (y : X.S), SSet.S.opEquiv
.symm y = { dim := y.dim, simplex := SSet.opObjEquiv.symm y.simplex }
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.op_δ`：op_δ (X : SSet.{u}) {n : Nat} (i : Fin (n + 2)) (x : X.op _⦋n
 + 1⦌) : X.op.δ i x = opObjEquiv.symm (X.δ i.rev (opObjEquiv x))
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_index`：δ_index : X.δ (hxy.index hd) (y.c
ast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex
· 使用定理 `Fin.rev_surjective`：rev_surjective : Surjective (@rev n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_eq_iff`：δ_eq_iff (i : Fin (d + 2)) : X.δ
 i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔ i = hxy.ind
ex hd
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.dim_eq`：dim_eq : y.dim = x.dim + 1
-/
lemma op : (S.opEquiv.symm x).IsUniquelyCodimOneFace (S.opEquiv.symm y) := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  simp only [opEquiv_symm_apply, iff]
  refine ⟨(hxy.index rfl).rev, by simpa using hxy.δ_index rfl, fun i hi ↦ ?_⟩
  obtain ⟨i, rfl⟩ := i.rev_surjective
  simpa [← hxy.δ_eq_iff rfl] using hi

set_option backward.defeqAttrib.useBackward true in
include hxy in
/-
**SSet.S.IsUniquelyCodimOneFace.of_iso** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsUniqu
elyCodimOneFace`。
形式化陈述：of_iso {Y : SSet.{u}} (e : X ≅ Y) : (S.mk (e.hom.app _ x.simplex)).IsUniqu
elyCodimOneFace (S.mk (e.hom.app _ y.simplex))
参数：e : X ≅ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.mk_surjective`：mk_surjective (s : X.S) : exists (n : Nat) (x : X 
_⦋n⦌), s = mk x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.iff`：iff {d : Nat} (x : X _⦋d⦌) (y : X _⦋d
 + 1⦌) : IsUniquelyCodimOneFace (S.mk x) (S.mk y) ↔ exists! (i : Fin (d + 2)), X
.δ i y = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.dim_eq`：dim_eq : y.dim = x.dim + 1
-/
lemma of_iso {Y : SSet.{u}} (e : X ≅ Y) :
    (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  rw [iff] at hxy ⊢
  simpa [← SSet.δ_naturality_apply, dsimp% (e.app (Opposite.op ⦋d⦌)).toEquiv.apply_eq_iff_eq]
/-
**SSet.S.IsUniquelyCodimOneFace.iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.IsU
niquelyCodimOneFace`。
形式化陈述：iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) (x y : X.S) : (S.mk (e.hom.app _ x.s
implex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) ↔ x.IsUniquelyCod
imOneFace y
参数：e : X ≅ Y；x y : X.S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_apply`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.of_iso`：of_iso {Y : SSet.{u}} (e : X ≅ Y) 
: (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.sim
plex))
-/
lemma iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) (x y : X.S) :
    (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) ↔
      x.IsUniquelyCodimOneFace y :=
  ⟨fun hxy' ↦ by simpa using hxy'.of_iso e.symm, fun hxy ↦ hxy.of_iso e⟩
/-
**SSet.S.IsUniquelyCodimOneFace.index_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S.I
sUniquelyCodimOneFace`。
形式化陈述：index_of_iso {Y : SSet.{u}} (e : X ≅ Y) {d : Nat} (hd : x.dim = d) : (hxy.
of_iso e).index hd = hxy.index hd
参数：e : X ≅ Y；hd : x.dim = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.of_iso`：of_iso {Y : SSet.{u}} (e : X ≅ Y) 
: (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.sim
plex))
· 使用引理 `SSet.S.mk_surjective`：mk_surjective (s : X.S) : exists (n : Nat) (x : X 
_⦋n⦌), s = mk x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_eq_iff`：δ_eq_iff (i : Fin (d + 2)) : X.δ
 i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔ i = hxy.ind
ex hd
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_index`：δ_index : X.δ (hxy.index hd) (y.c
ast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.dim_eq`：dim_eq : y.dim = x.dim + 1
-/
lemma index_of_iso {Y : SSet.{u}} (e : X ≅ Y) {d : ℕ} (hd : x.dim = d) :
    (hxy.of_iso e).index hd = hxy.index hd := by
  obtain ⟨dx, x, rfl⟩ := x.mk_surjective
  obtain ⟨dy, y, rfl⟩ := y.mk_surjective
  obtain rfl : dy = dx + 1 := hxy.dim_eq
  obtain rfl : dx = d := hd
  symm
  simp [← (hxy.of_iso e).δ_eq_iff rfl,
    ← SSet.δ_naturality_apply, dsimp% hxy.δ_index rfl]

end IsUniquelyCodimOneFace

end SSet.S

