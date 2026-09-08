/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Paths in simplicial sets

A path in a simplicial set `X` of length `n` is a directed path comprised of
`n + 1` 0-simplices and `n` 1-simplices, together with identifications between
0-simplices and the sources and targets of the 1-simplices. We define this
construction first for truncated simplicial sets in `SSet.Truncated.Path`. A
path in a simplicial set `X` is then defined as a 1-truncated path in the
1-truncation of `X`.

An `n`-simplex has a maximal path, the `spine` of the simplex, which is a path
of length `n`.
-/

@[expose] public section

universe v u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet
namespace Truncated

open SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

/-- A path of length `n` in a 1-truncated simplicial set `X` is a directed path
of `n` edges. -/
@[ext]
/-
**SSet.Truncated.Path** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：Path {n : Nat} (X : SSet.Truncated.{u} (n + 1)) (m : Nat)
参数：X : SSet.Truncated.{u} (n + 1)；m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path of length `n` in a 1-truncated simplicial set `X` is a directed path
of `n` edges.
-/
structure Path₁ (X : SSet.Truncated.{u} 1) (n : ℕ) where
  /-- A path includes the data of `n + 1` 0-simplices in `X`. -/
  vertex : Fin (n + 1) → X _⦋0⦌₁
  /-- A path includes the data of `n` 1-simplices in `X`. -/
  arrow : Fin n → X _⦋1⦌₁
  /-- The source of a 1-simplex in a path is identified with the source vertex. -/
  arrow_src (i : Fin n) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  /-- The target of a 1-simplex in a path is identified with the target vertex. -/
  arrow_tgt (i : Fin n) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

/-- A path of length `m` in an `n + 1`-truncated simplicial set `X` is given by
the data of a `Path₁` structure on the further 1-truncation of `X`. -/
/-
**SSet.Truncated.Path** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：Path {n : Nat} (X : SSet.Truncated.{u} (n + 1)) (m : Nat)
参数：X : SSet.Truncated.{u} (n + 1)；m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path of length `m` in an `n + 1`-truncated simplicial set `X` is given by
the data of a `Path₁` structure on the further 1-truncation of `X`.
-/
def Path {n : ℕ} (X : SSet.Truncated.{u} (n + 1)) (m : ℕ) :=
  trunc (n + 1) 1 |>.obj X |>.Path₁ m

namespace Path

variable {n : ℕ} {X : SSet.Truncated.{u} (n + 1)} {m : ℕ}

/-- A path includes the data of `n + 1` 0-simplices in `X`. -/
/-
**SSet.Truncated.Path.vertex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：vertex (f : Path X m) (i : Fin (m + 1)) : X _⦋0⦌ₙ₊₁
参数：f : Path X m；i : Fin (m + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path includes the data of `n + 1` 0-simplices in `X`.
-/
abbrev vertex (f : Path X m) (i : Fin (m + 1)) : X _⦋0⦌ₙ₊₁ :=
  Path₁.vertex f i

/-- A path includes the data of `n` 1-simplices in `X`. -/
/-
**SSet.Truncated.Path.arrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：arrow (f : Path X m) (i : Fin m) : X _⦋1⦌ₙ₊₁
参数：f : Path X m；i : Fin m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path includes the data of `n` 1-simplices in `X`.
-/
abbrev arrow (f : Path X m) (i : Fin m) : X _⦋1⦌ₙ₊₁ :=
  Path₁.arrow f i

/-- The source of a 1-simplex in a path is identified with the source vertex. -/
/-
**SSet.Truncated.Path.arrow_src** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：arrow_src (f : Path X m) (i : Fin m) : X.map (tr (δ 1)).op (f.arrow i) = f
.vertex i.castSucc
参数：f : Path X m；i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Path₁.arrow_src`：∀ {X : SSet.Truncated 1} {n : ℕ} (self :
 X.Path₁ n) (i : Fin n),   (CategoryTheory.ConcreteCategory.hom         (X.map  
         (SimplexCat…

--- 原说明 ---
The source of a 1-simplex in a path is identified with the source vertex.
-/
lemma arrow_src (f : Path X m) (i : Fin m) :
    X.map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc :=
  Path₁.arrow_src f i

/-- The target of a 1-simplex in a path is identified with the target vertex. -/
/-
**SSet.Truncated.Path.arrow_tgt** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：arrow_tgt (f : Path X m) (i : Fin m) : X.map (tr (δ 0)).op (f.arrow i) = f
.vertex i.succ
参数：f : Path X m；i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Path₁.arrow_tgt`：∀ {X : SSet.Truncated 1} {n : ℕ} (self :
 X.Path₁ n) (i : Fin n),   (CategoryTheory.ConcreteCategory.hom         (X.map  
         (SimplexCat…

--- 原说明 ---
The target of a 1-simplex in a path is identified with the target vertex.
-/
lemma arrow_tgt (f : Path X m) (i : Fin m) :
    X.map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ :=
  Path₁.arrow_tgt f i

@[ext]
/-
**SSet.Truncated.Path.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：ext {f g : Path X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
 f = g
参数：hᵥ : f.vertex = g.vertex；hₐ : f.arrow = g.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Path₁.ext`：∀ {X : SSet.Truncated 1} {n : ℕ} {x y : X.Path
₁ n}, x.vertex = y.vertex → x.arrow = y.arrow → x = y
-/
lemma ext {f g : Path X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  Path₁.ext hᵥ hₐ

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
/-
**SSet.Truncated.Path.ext'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：ext' {f g : Path X (m + 1)} (h : forall i, f.arrow i = g.arrow i) : f = g
参数：m + 1；h : forall i, f.arrow i = g.arrow i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.ext`：ext {f g : Path X m} (hᵥ : f.vertex = g.vertex)
 (hₐ : f.arrow = g.arrow) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Truncated.Path.arrow_src`：arrow_src (f : Path X m) (i : Fin m) : X.
map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SSet.Truncated.Path.arrow_tgt`：arrow_tgt (f : Path X m) (i : Fin m) : X.
map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ

--- 原说明 ---
To show two paths equal it suffices to show that they have the same edges.
-/
lemma ext' {f g : Path X (m + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m), ← g.arrow_tgt (Fin.last m), h]
  · exact h j

/-- Constructor for paths of length `2` from two paths of length `1`. -/
@[simps!]
/-
**SSet.Truncated.Path.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for paths of length `2` from two paths of length `1`.
-/
def mk₂ {n : ℕ} {X : Truncated.{u} (n + 1)} (p q : X.Path 1)
  (h : p.vertex 1 = q.vertex 0) : X.Path 2 where
  vertex := ![p.vertex 0, p.vertex 1, q.vertex 1]
  arrow := ![p.arrow 0, q.arrow 0]
  arrow_src i := by
    fin_cases i
    · exact p.arrow_src 0
    · exact (q.arrow_src 0).trans h.symm
  arrow_tgt i := by
    fin_cases i
    · exact p.arrow_tgt 0
    · exact q.arrow_tgt 0

/-- For `j + l ≤ m`, a path of length `m` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
/-
**SSet.Truncated.Path.interval** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：interval (f : Path X m) (j l : Nat) (h : j + l <= m
参数：f : Path X m；j l : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `j + l ≤ m`, a path of length `m` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`.
-/
def interval (f : Path X m) (j l : ℕ) (h : j + l ≤ m := by omega) : Path X l where
  vertex i := f.vertex ⟨j + i, by lia⟩
  arrow i := f.arrow ⟨j + i, by lia⟩
  arrow_src i := f.arrow_src ⟨j + i, by lia⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by lia⟩

variable {X Y : SSet.Truncated.{u} (n + 1)} {m : ℕ}

/-- Maps of `n + 1`-truncated simplicial sets induce maps of paths. -/
/-
**SSet.Truncated.Path.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：map (f : Path X m) (σ : X ⟶ Y) : Path Y m where vertex i
参数：f : Path X m；σ : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps of `n + 1`-truncated simplicial sets induce maps of paths.
-/
def map (f : Path X m) (σ : X ⟶ Y) : Path Y m where
  vertex i := σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i)
  arrow i := σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
    exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 1)).op) _ |>.symm
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
    exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 0)).op) _ |>.symm

/- We write this lemma manually to ensure it refers to `Path.vertex`. -/
@[simp]
/-
**SSet.Truncated.Path.map_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Path`
。
形式化陈述：map_vertex (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1)) : (f.map σ).vertex
 i = σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i)
参数：f : Path X m；σ : X ⟶ Y；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We write this lemma manually to ensure it refers to `Path.vertex`.
-/
lemma map_vertex (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1)) :
    (f.map σ).vertex i = σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i) :=
  rfl

/- We write this lemma manually to ensure it refers to `Path.arrow`. -/
@[simp]
/-
**SSet.Truncated.Path.map_arrow** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Path`。
形式化陈述：map_arrow (f : Path X m) (σ : X ⟶ Y) (i : Fin m) : (f.map σ).arrow i = σ.a
pp (op ⦋1⦌ₙ₊₁) (f.arrow i)
参数：f : Path X m；σ : X ⟶ Y；i : Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We write this lemma manually to ensure it refers to `Path.arrow`.
-/
lemma map_arrow (f : Path X m) (σ : X ⟶ Y) (i : Fin m) :
    (f.map σ).arrow i = σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i) :=
  rfl
/-
**SSet.Truncated.Path.map_interval** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Pat
h`。
形式化陈述：map_interval (f : Path X m) (σ : X ⟶ Y) (j l : Nat) (h : j + l <= m) : (f.
map σ).interval j l h = (f.interval j l h).map σ
参数：f : Path X m；σ : X ⟶ Y；j l : Nat；h : j + l <= m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_interval (f : Path X m) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- The spine of an `m`-simplex in `X` is the path of edges of length `m`
formed by traversing in order through its vertices. -/
/-
**SSet.Truncated.spine** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：spine (m : Nat) (h : m <= n + 1
参数：m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spine of an `m`-simplex in `X` is the path of edges of length `m`
formed by traversing in order through its vertices.
-/
def spine (m : ℕ) (h : m ≤ n + 1 := by omega) (Δ : X _⦋m⦌ₙ₊₁) : Path X m where
  vertex i := X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ
  arrow i := X.map (tr (mkOfSucc i)).op Δ
  arrow_src i := by
    simp [← δ_one_mkOfSucc, tr_comp]
    rfl
  arrow_tgt i := by
    simp [← δ_zero_mkOfSucc, tr_comp]
    rfl

/-- Further truncating `X` above `m` does not change the `m`-spine. -/
/-
**SSet.Truncated.trunc_spine** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：trunc_spine (k m : Nat) (h : m <= k + 1) (hₙ : k <= n) : ((trunc (n + 1) (
k + 1)).obj X).spine m = X.spine m
参数：k m : Nat；h : m <= k + 1；hₙ : k <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further truncating `X` above `m` does not change the `m`-spine.
-/
lemma trunc_spine (k m : ℕ) (h : m ≤ k + 1) (hₙ : k ≤ n) :
    ((trunc (n + 1) (k + 1)).obj X).spine m = X.spine m :=
  rfl

variable (m : ℕ) (hₘ : m ≤ n + 1)

/- We write this lemma manually to ensure it refers to `Path.vertex`. -/
@[simp]
/-
**SSet.Truncated.spine_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：spine_vertex (Δ : X _⦋m⦌ₙ₊₁) (i : Fin (m + 1)) : (X.spine m hₘ Δ).vertex i
 = X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ
参数：Δ : X _⦋m⦌ₙ₊₁；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We write this lemma manually to ensure it refers to `Path.vertex`.
-/
lemma spine_vertex (Δ : X _⦋m⦌ₙ₊₁) (i : Fin (m + 1)) :
    (X.spine m hₘ Δ).vertex i =
      X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ :=
  rfl

/- We write this lemma manually to ensure it refers to `Path.arrow`. -/
@[simp]
/-
**SSet.Truncated.spine_arrow** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：spine_arrow (Δ : X _⦋m⦌ₙ₊₁) (i : Fin m) : (X.spine m hₘ Δ).arrow i = X.map
 (tr (mkOfSucc i)).op Δ
参数：Δ : X _⦋m⦌ₙ₊₁；i : Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We write this lemma manually to ensure it refers to `Path.arrow`.
-/
lemma spine_arrow (Δ : X _⦋m⦌ₙ₊₁) (i : Fin m) :
    (X.spine m hₘ Δ).arrow i = X.map (tr (mkOfSucc i)).op Δ :=
  rfl
/-
**SSet.Truncated.spine_map_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：spine_map_vertex (Δ : X _⦋m⦌ₙ₊₁) (a : Nat) (hₐ : a <= n + 1) (φ : ⦋a⦌ₙ₊₁ ⟶
 ⦋m⦌ₙ₊₁) (i : Fin (a + 1)) : (X.spine a hₐ (X.map φ.op Δ)).vertex i = (X.spine m
 hₘ Δ).vertex (φ.hom.toOrderHom i)
参数：Δ : X _⦋m⦌ₙ₊₁；a : Nat；hₐ : a <= n + 1；φ : ⦋a⦌ₙ₊₁ ⟶ ⦋m⦌ₙ₊₁；i : Fin (a + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `SimplexCategory.Truncated.Hom.tr_comp'`：∀ {n : ℕ} {a b c : SimplexCatego
ry} (f : a ⟶ b) {hb : b.len ≤ n} {hc : c.len ≤ n}   (g : { obj := b, property :=
 hb } ⟶ { obj := c, property…
· 使用定理 `SimplexCategory.const_comp`：const_comp (x : SimplexCategory) {y z : Simp
lexCategory} (f : y ⟶ z) (i : Fin (y.len + 1)) : const x y i ≫ f = const x z (f.
toOrderHom i)
-/
lemma spine_map_vertex (Δ : X _⦋m⦌ₙ₊₁) (a : ℕ) (hₐ : a ≤ n + 1)
    (φ : ⦋a⦌ₙ₊₁ ⟶ ⦋m⦌ₙ₊₁) (i : Fin (a + 1)) :
    (X.spine a hₐ (X.map φ.op Δ)).vertex i =
      (X.spine m hₘ Δ).vertex (φ.hom.toOrderHom i) := by
  dsimp only [spine_vertex]
  rw [← Functor.map_comp_apply, ← op_comp, ← tr_comp',
    SimplexCategory.const_comp]
/-
**SSet.Truncated.spine_map_subinterval** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated
`。
形式化陈述：spine_map_subinterval (j l : Nat) (h : j + l <= m) (Δ : X _⦋m⦌ₙ₊₁) : X.spi
ne l (by lia) (X.map (tr (subinterval j l h)).op Δ) = (X.spine m hₘ Δ).interval 
j l h
参数：j l : Nat；h : j + l <= m；Δ : X _⦋m⦌ₙ₊₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.ext`：ext {f g : Path X m} (hᵥ : f.vertex = g.vertex)
 (hₐ : f.arrow = g.arrow) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `SimplexCategory.Truncated.Hom.tr_comp`：∀ {n : ℕ} {a b c : SimplexCategor
y} (f : a ⟶ b) (g : b ⟶ c)   (ha : autoParam (a.len ≤ n) SimplexCategory.Truncat
ed.Hom.tr_comp._auto_1)   (…
· 使用定理 `lt_add_of_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddRightMono α] {a b c d : α}, a < b + c → b ≤ d → a < d + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用引理 `SimplexCategory.const_subinterval_eq`：const_subinterval_eq {n} (j l : Na
t) (hjl : j + l <= n) (i : Fin (l + 1)) : ⦋0⦌.const ⦋l⦌ i ≫ subinterval j l hjl 
= ⦋0⦌.const ⦋n⦌ ⟨j + i.1, …
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用引理 `SimplexCategory.mkOfSucc_subinterval_eq`：mkOfSucc_subinterval_eq {n} (j 
l : Nat) (hjl : j + l <= n) (i : Fin l) : mkOfSucc i ≫ subinterval j l hjl = mkO
fSucc ⟨j + i.1, Nat.lt_of_lt_…
-/
lemma spine_map_subinterval (j l : ℕ) (h : j + l ≤ m) (Δ : X _⦋m⦌ₙ₊₁) :
    X.spine l (by lia) (X.map (tr (subinterval j l h)).op Δ) =
      (X.spine m hₘ Δ).interval j l h := by
  ext i
  · dsimp only [spine_vertex, Path.interval]
    rw [← Functor.map_comp_apply, ← op_comp, ← tr_comp,
      const_subinterval_eq]
  · dsimp only [spine_arrow, Path.interval]
    rw [← Functor.map_comp_apply, ← op_comp, ← tr_comp,
      mkOfSucc_subinterval_eq]

end Truncated

/-- A path of length `n` in a simplicial set `X` is defined as a 1-truncated
path in the 1-truncation of `X`. -/
/-
**SSet.Path** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → ℕ → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path of length `n` in a simplicial set `X` is defined as a 1-truncated
path in the 1-truncation of `X`.
-/
abbrev Path (X : SSet.{u}) (n : ℕ) := truncation 1 |>.obj X |>.Path n

namespace Path

variable {X : SSet.{u}} {n : ℕ}

/-- A path includes the data of `n + 1` 0-simplices in `X`. -/
/-
**SSet.Path.vertex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Path`。
形式化陈述：vertex (f : Path X n) (i : Fin (n + 1)) : X _⦋0⦌
参数：f : Path X n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path includes the data of `n + 1` 0-simplices in `X`.
-/
abbrev vertex (f : Path X n) (i : Fin (n + 1)) : X _⦋0⦌ :=
  Truncated.Path.vertex f i

/-- A path includes the data of `n` 1-simplices in `X`. -/
/-
**SSet.Path.arrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Path`。
形式化陈述：arrow (f : Path X n) (i : Fin n) : X _⦋1⦌
参数：f : Path X n；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path includes the data of `n` 1-simplices in `X`.
-/
abbrev arrow (f : Path X n) (i : Fin n) : X _⦋1⦌ :=
  Truncated.Path.arrow f i
/-
**SSet.Path.congr_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：congr_vertex {f g : Path X n} (h : f = g) (i : Fin (n + 1)) : f.vertex i =
 g.vertex i
参数：h : f = g；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_vertex {f g : Path X n} (h : f = g) (i : Fin (n + 1)) :
    f.vertex i = g.vertex i := by rw [h]
/-
**SSet.Path.congr_arrow** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：congr_arrow {f g : Path X n} (h : f = g) (i : Fin n) : f.arrow i = g.arrow
 i
参数：h : f = g；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_arrow {f g : Path X n} (h : f = g) (i : Fin n) :
    f.arrow i = g.arrow i := by rw [h]

/-- The source of a 1-simplex in a path is identified with the source vertex. -/
/-
**SSet.Path.arrow_src** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：arrow_src (f : Path X n) (i : Fin n) : X.δ 1 (f.arrow i) = f.vertex i.cast
Succ
参数：f : Path X n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.arrow_src`：arrow_src (f : Path X m) (i : Fin m) : X.
map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc

--- 原说明 ---
The source of a 1-simplex in a path is identified with the source vertex.
-/
lemma arrow_src (f : Path X n) (i : Fin n) :
    X.δ 1 (f.arrow i) = f.vertex i.castSucc :=
  Truncated.Path.arrow_src f i

/-- The target of a 1-simplex in a path is identified with the target vertex. -/
/-
**SSet.Path.arrow_tgt** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：arrow_tgt (f : Path X n) (i : Fin n) : X.δ 0 (f.arrow i) = f.vertex i.succ
参数：f : Path X n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.arrow_tgt`：arrow_tgt (f : Path X m) (i : Fin m) : X.
map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ

--- 原说明 ---
The target of a 1-simplex in a path is identified with the target vertex.
-/
lemma arrow_tgt (f : Path X n) (i : Fin n) :
    X.δ 0 (f.arrow i) = f.vertex i.succ :=
  Truncated.Path.arrow_tgt f i

@[ext]
/-
**SSet.Path.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：ext {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
 f = g
参数：hᵥ : f.vertex = g.vertex；hₐ : f.arrow = g.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.ext`：ext {f g : Path X m} (hᵥ : f.vertex = g.vertex)
 (hₐ : f.arrow = g.arrow) : f = g
-/
lemma ext {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  Truncated.Path.ext hᵥ hₐ

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
/-
**SSet.Path.ext'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：ext' {f g : Path X (n + 1)} (h : forall i, f.arrow i = g.arrow i) : f = g
参数：n + 1；h : forall i, f.arrow i = g.arrow i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.ext'`：ext' {f g : Path X (m + 1)} (h : forall i, f.a
rrow i = g.arrow i) : f = g

--- 原说明 ---
To show two paths equal it suffices to show that they have the same edges.
-/
lemma ext' {f g : Path X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Truncated.Path.ext' h

@[ext]
/-
**SSet.Path.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：ext {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
 f = g
参数：hᵥ : f.vertex = g.vertex；hₐ : f.arrow = g.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Path.ext`：ext {f g : Path X m} (hᵥ : f.vertex = g.vertex)
 (hₐ : f.arrow = g.arrow) : f = g
-/
lemma ext₀ {f g : Path X 0} (h : f.vertex 0 = g.vertex 0) : f = g := by
  ext i
  · fin_cases i; exact h
  · fin_cases i

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
/-
**SSet.Path.interval** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Path`。
形式化陈述：interval (f : Path X n) (j l : Nat) (h : j + l <= n
参数：f : Path X n；j l : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`.
-/
def interval (f : Path X n) (j l : ℕ) (h : j + l ≤ n := by grind) : Path X l :=
  Truncated.Path.interval f j l h
/-
**SSet.Path.arrow_interval** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：arrow_interval (f : Path X n) (j l : Nat) (k' : Fin l) (k : Fin n) (h : j 
+ l <= n
参数：f : Path X n；j l : Nat；k' : Fin l；k : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma arrow_interval (f : Path X n) (j l : ℕ) (k' : Fin l) (k : Fin n)
    (h : j + l ≤ n := by lia) (hkk' : j + k' = k := by grind) :
    (f.interval j l h).arrow k' = f.arrow k := by
  dsimp [interval, arrow, Truncated.Path.interval, Truncated.Path.arrow]
  congr

variable {X Y : SSet.{u}} {n : ℕ}

/-- Maps of simplicial sets induce maps of paths in a simplicial set. -/
/-
**SSet.Path.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Path`。
形式化陈述：map (f : Path X n) (σ : X ⟶ Y) : Path Y n
参数：f : Path X n；σ : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps of simplicial sets induce maps of paths in a simplicial set.
-/
def map (f : Path X n) (σ : X ⟶ Y) : Path Y n :=
  Truncated.Path.map f ((truncation 1).map σ)

@[simp]
/-
**SSet.Path.map_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：map_vertex (f : Path X n) (σ : X ⟶ Y) (i : Fin (n + 1)) : (f.map σ).vertex
 i = σ.app (op ⦋0⦌) (f.vertex i)
参数：f : Path X n；σ : X ⟶ Y；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_vertex (f : Path X n) (σ : X ⟶ Y) (i : Fin (n + 1)) :
    (f.map σ).vertex i = σ.app (op ⦋0⦌) (f.vertex i) :=
  rfl

@[simp]
/-
**SSet.Path.map_arrow** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：map_arrow (f : Path X n) (σ : X ⟶ Y) (i : Fin n) : (f.map σ).arrow i = σ.a
pp (op ⦋1⦌) (f.arrow i)
参数：f : Path X n；σ : X ⟶ Y；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_arrow (f : Path X n) (σ : X ⟶ Y) (i : Fin n) :
    (f.map σ).arrow i = σ.app (op ⦋1⦌) (f.arrow i) :=
  rfl

/-- `Path.map` respects subintervals of paths. -/
/-
**SSet.Path.map_interval** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Path`。
形式化陈述：map_interval (f : Path X n) (σ : X ⟶ Y) (j l : Nat) (h : j + l <= n) : (f.
map σ).interval j l h = (f.interval j l h).map σ
参数：f : Path X n；σ : X ⟶ Y；j l : Nat；h : j + l <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Path.map` respects subintervals of paths.
-/
lemma map_interval (f : Path X n) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

section spine

variable (X : SSet.{u}) (n : ℕ)

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n` formed
by traversing in order through the vertices of `X _⦋n⦌ₙ₊₁`. -/
/-
**SSet.spine** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：spine : X _⦋n⦌ -> Path X n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spine of an `n`-simplex in `X` is the path of edges of length `n` formed
by traversing in order through the vertices of `X _⦋n⦌ₙ₊₁`.
-/
def spine : X _⦋n⦌ → Path X n :=
  truncation (n + 1) |>.obj X |>.spine n

@[simp]
/-
**SSet.spine_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：spine_vertex (Δ : X _⦋n⦌) (i : Fin (n + 1)) : (X.spine n Δ).vertex i = X.m
ap (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op Δ
参数：Δ : X _⦋n⦌；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spine_vertex (Δ : X _⦋n⦌) (i : Fin (n + 1)) :
    (X.spine n Δ).vertex i = X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op Δ :=
  rfl

@[simp]
/-
**SSet.spine_arrow** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：spine_arrow (Δ : X _⦋n⦌) (i : Fin n) : (X.spine n Δ).arrow i = X.map (mkOf
Succ i).op Δ
参数：Δ : X _⦋n⦌；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spine_arrow (Δ : X _⦋n⦌) (i : Fin n) :
    (X.spine n Δ).arrow i = X.map (mkOfSucc i).op Δ :=
  rfl
/-
**SSet.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spine_δ₀ {m : ℕ} (x : X _⦋m + 1⦌) :
    X.spine m (X.δ 0 x) = (X.spine (m + 1) x).interval 1 m := by
  obtain _ | m := m
  · ext
    simp [spine, Path.vertex, Truncated.Path.vertex,
      Truncated.spine, Path.interval, Truncated.Path.interval,
      Truncated.Hom.tr, ← SimplexCategory.δ_zero_eq_const]
    rfl
  · ext i
    dsimp
    rw [SimplicialObject.δ_def, ← Functor.map_comp_apply, ← op_comp,
      SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp)]
    symm
    exact Path.arrow_interval _ _ _ _ _ _ (by rw [Fin.val_succ, add_comm])

/-- For `m ≤ n + 1`, the `m`-spine of `X` factors through the `n + 1`-truncation
of `X`. -/
/-
**SSet.truncation_spine** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：truncation_spine (m : Nat) (h : m <= n + 1) : ((truncation (n + 1)).obj X)
.spine m = X.spine m
参数：m : Nat；h : m <= n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `m ≤ n + 1`, the `m`-spine of `X` factors through the `n + 1`-truncation
of `X`.
-/
lemma truncation_spine (m : ℕ) (h : m ≤ n + 1) :
    ((truncation (n + 1)).obj X).spine m = X.spine m :=
  rfl
/-
**SSet.spine_map_vertex** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：spine_map_vertex (Δ : X _⦋n⦌) {m : Nat} (φ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) 
: (X.spine m (X.map φ.op Δ)).vertex i = (X.spine n Δ).vertex (φ.toOrderHom i)
参数：Δ : X _⦋n⦌；φ : ⦋m⦌ ⟶ ⦋n⦌；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.spine_map_vertex`：spine_map_vertex (Δ : X _⦋m⦌ₙ₊₁) (a : N
at) (hₐ : a <= n + 1) (φ : ⦋a⦌ₙ₊₁ ⟶ ⦋m⦌ₙ₊₁) (i : Fin (a + 1)) : (X.spine a hₐ (X
.map φ.op Δ)).vertex …
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma spine_map_vertex (Δ : X _⦋n⦌) {m : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (X.spine m (X.map φ.op Δ)).vertex i =
      (X.spine n Δ).vertex (φ.toOrderHom i) :=
  truncation (max m n + 1) |>.obj X
    |>.spine_map_vertex n (by omega) Δ m (by omega) (InducedCategory.homMk φ) i
/-
**SSet.spine_map_subinterval** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：spine_map_subinterval (j l : Nat) (h : j + l <= n) (Δ : X _⦋n⦌) : X.spine 
l (X.map (subinterval j l h).op Δ) = (X.spine n Δ).interval j l h
参数：j l : Nat；h : j + l <= n；Δ : X _⦋n⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.spine_map_subinterval`：spine_map_subinterval (j l : Nat) 
(h : j + l <= m) (Δ : X _⦋m⦌ₙ₊₁) : X.spine l (by lia) (X.map (tr (subinterval j 
l h)).op Δ) = (X.spine m h…
-/
lemma spine_map_subinterval (j l : ℕ) (h : j + l ≤ n) (Δ : X _⦋n⦌) :
    X.spine l (X.map (subinterval j l h).op Δ) = (X.spine n Δ).interval j l h :=
  truncation (n + 1) |>.obj X |>.spine_map_subinterval n (by lia) j l h Δ

end spine

/-- The spine of the unique non-degenerate `n`-simplex in `Δ[n]`. -/
/-
**SSet.stdSimplex.spineId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：(n : ℕ) → (SSet.stdSimplex.obj { len := n }).Path n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The spine of the unique non-degenerate `n`-simplex in `Δ[n]`.
-/
def stdSimplex.spineId (n : ℕ) : Path Δ[n] n :=
  spine Δ[n] n (objEquiv.symm (𝟙 _))

@[simp]
/-
**SSet.stdSimplex.spineId_vertex** 是 Mathlib 中的一个定理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：∀ (n : ℕ) (i : Fin (n + 1)), (SSet.stdSimplex.spineId n).vertex i = SSet.s
tdSimplex.obj₀Equiv.symm i
参数：n : ℕ；i : Fin (n + 1)；SSet.stdSimplex.spineId n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stdSimplex.spineId_vertex (n : ℕ) (i : Fin (n + 1)) :
    (stdSimplex.spineId n).vertex i = obj₀Equiv.symm i := rfl

@[simp]
/-
**SSet.stdSimplex.spineId_arrow_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `SSet.stdSi
mplex`。
形式化陈述：∀ (n : ℕ) (i : Fin n), ((SSet.stdSimplex.spineId n).arrow i) 0 = i.castSuc
c
参数：n : ℕ；i : Fin n；(SSet.stdSimplex.spineId n).arrow i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma stdSimplex.spineId_arrow_apply_zero (n : ℕ) (i : Fin n) :
    (stdSimplex.spineId n).arrow i 0 = i.castSucc := rfl

@[simp]
/-
**SSet.stdSimplex.spineId_arrow_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `SSet.stdSim
plex`。
形式化陈述：∀ (n : ℕ) (i : Fin n), ((SSet.stdSimplex.spineId n).arrow i) 1 = i.succ
参数：n : ℕ；i : Fin n；(SSet.stdSimplex.spineId n).arrow i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma stdSimplex.spineId_arrow_apply_one (n : ℕ) (i : Fin n) :
    (stdSimplex.spineId n).arrow i 1 = i.succ := rfl

/-- A path of a simplicial set can be lifted to a subcomplex if the vertices
and arrows belong to this subcomplex. -/
@[simps]
/-
**SSet.Subcomplex.liftPath** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：{X : _root_.SSet} →   (A : X.Subcomplex) →     {n : ℕ} →       (p : X.Path
 n) →         (∀ (j : Fin (n + 1)), p.vertex j ∈ A.obj (Opposite.op { len := 0 }
)) →           (∀ (j : Fin n), p.arrow j ∈ A.obj (Opposite.op { len := 1 })) → A
.toSSet.Path n
参数：A : X.Subcomplex；p : X.Path n；∀ (j : Fin (n + 1)), p.vertex j ∈ A.obj (Opposi
te.op { len := 0 })；∀ (j : Fin n), p.arrow j ∈ A.obj (Opposite.op { len := 1 })。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path of a simplicial set can be lifted to a subcomplex if the vertices
and arrows belong to this subcomplex.
-/
def Subcomplex.liftPath {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ} (p : Path X n)
    (hp₀ : ∀ j, p.vertex j ∈ A.obj _)
    (hp₁ : ∀ j, p.arrow j ∈ A.obj _) :
    Path A n where
  vertex j := ⟨p.vertex j, hp₀ _⟩
  arrow j := ⟨p.arrow j, hp₁ _⟩
  arrow_src j := Subtype.ext <| p.arrow_src j
  arrow_tgt j := Subtype.ext <| p.arrow_tgt j

@[simp]
/-
**SSet.Subcomplex.map_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subcomplex.map_ι_liftPath {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ} (p : Path X n)
    (hp₀ : ∀ j, p.vertex j ∈ A.obj _)
    (hp₁ : ∀ j, p.arrow j ∈ A.obj _) :
    (A.liftPath p hp₀ hp₁).map A.ι = p := rfl

/-- Any inner horn contains the spine of the unique non-degenerate `n`-simplex
in `Δ[n]`. -/
@[simps! vertex_coe arrow_coe]
/-
**SSet.horn.spineId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：{n : ℕ} → (i : Fin (n + 3)) → 0 < i → i < Fin.last (n + 2) → (SSet.horn (n
 + 2) i).toSSet.Path (n + 2)
参数：i : Fin (n + 3)；n + 2；SSet.horn (n + 2) i；n + 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any inner horn contains the spine of the unique non-degenerate `n`-simplex
in `Δ[n]`.
-/
def horn.spineId {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path (Λ[n + 2, i] : SSet.{u}) (n + 2) :=
  Λ[n + 2, i].liftPath (stdSimplex.spineId (n + 2)) (by simp) (fun j ↦ by
    convert! (horn.primitiveEdge.{u} h₀ hₙ j).2
    ext a
    fin_cases a <;> rfl)

@[simp]
/-
**SSet.horn.spineId_map_hornInclusion** 是 Mathlib 中的一个定理，位于命名空间 `SSet.horn`。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 3)) (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)),   (S
Set.horn.spineId i h₀ hₙ).map (SSet.horn (n + 2) i).ι = SSet.stdSimplex.spineId 
(n + 2)
参数：i : Fin (n + 3)；h₀ : 0 < i；hₙ : i < Fin.last (n + 2)；SSet.horn.spineId i h₀ h
ₙ；SSet.horn (n + 2) i；n + 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma horn.spineId_map_hornInclusion {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path.map (horn.spineId.{u} i h₀ hₙ) Λ[n + 2, i].ι =
      stdSimplex.spineId (n + 2) := rfl

end SSet

