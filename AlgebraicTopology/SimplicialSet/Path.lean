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
/--
Definition of `Path₁` / `Path₁` 的定义

English:
structure Path₁
  parameters: (X : SSet.Truncated.{u} 1) (n : Nat)
  axioms and operations (4):
    - vertex : Fin (n + 1) -> X _⦋0⦌₁
    - arrow : Fin n -> X _⦋1⦌₁
    - arrow_src((i : Fin n)) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
    - arrow_tgt((i : Fin n)) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

中文:
结构 Path₁
  参数: (X : SSet.Truncated.{u} 1) (n : 自然数)
  公理与运算 (4 个):
    - vertex : 有限集 (n + 1) -> X _⦋0⦌₁
    - arrow : 有限集 n -> X _⦋1⦌₁
    - arrow_src((i : 有限集 n)) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
    - arrow_tgt((i : 有限集 n)) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ
-/
structure Path₁ (X : SSet.Truncated.{u} 1) (n : Nat) where
  /-- A path includes the data of `n + 1` 0-simplices in `X`. -/
  vertex : Fin (n + 1) -> X _⦋0⦌₁
  /-- A path includes the data of `n` 1-simplices in `X`. -/
  arrow : Fin n -> X _⦋1⦌₁
  /-- The source of a 1-simplex in a path is identified with the source vertex. -/
  arrow_src (i : Fin n) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  /-- The target of a 1-simplex in a path is identified with the target vertex. -/
  arrow_tgt (i : Fin n) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

/--
Definition of `Path` / `Path` 的定义

English:
definition Path
  signature: {n : Nat} (X : SSet.Truncated.{u} (n + 1)) (m : Nat)
  body: .Path₁ m .obj X trunc (n + 1) 1

中文:
定义 道路
  签名: {n : 自然数} (X : SSet.Truncated.{u} (n + 1)) (m : 自然数)
  定义体: .Path₁ m .obj X trunc (n + 1) 1
-/
def Path {n : Nat} (X : SSet.Truncated.{u} (n + 1)) (m : Nat) :=
.Path₁ m .obj X trunc (n + 1) 1

namespace Path

variable {n : Nat} {X : SSet.Truncated.{u} (n + 1)} {m : Nat}

/--
Definition of `vertex` / `vertex` 的定义

English:
abbreviation vertex
  signature: (f : Path X m) (i : Fin (m + 1))
  body: Path₁.vertex f i

中文:
缩写 vertex
  签名: (f : 道路 X m) (i : 有限集 (m + 1))
  定义体: Path₁.vertex f i

Depends on / 依赖: vertex
-/
abbrev vertex (f : Path X m) (i : Fin (m + 1)) : X _⦋0⦌ₙ₊₁ :=
  Path₁.vertex f i

/--
Definition of `arrow` / `arrow` 的定义

English:
abbreviation arrow
  signature: (f : Path X m) (i : Fin m)
  body: Path₁.arrow f i

中文:
缩写 arrow
  签名: (f : 道路 X m) (i : 有限集 m)
  定义体: Path₁.arrow f i
-/
abbrev arrow (f : Path X m) (i : Fin m) : X _⦋1⦌ₙ₊₁ :=
  Path₁.arrow f i

/--
lemma `arrow_src` / 引理 `arrow_src`

English:
lemma arrow_src
  given: (f : Path X m) (i : Fin m)
  proof: Path₁.arrow_src f i

中文:
引理 arrow_src
  条件: (f : 道路 X m) (i : 有限集 m)
  证明: Path₁.arrow_src f i

Depends on / 依赖: arrow_src
-/
lemma arrow_src (f : Path X m) (i : Fin m) :
    X.map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc :=
  Path₁.arrow_src f i

/--
lemma `arrow_tgt` / 引理 `arrow_tgt`

English:
lemma arrow_tgt
  given: (f : Path X m) (i : Fin m)
  proof: Path₁.arrow_tgt f i

@[ext]

中文:
引理 arrow_tgt
  条件: (f : 道路 X m) (i : 有限集 m)
  证明: Path₁.arrow_tgt f i

@[ext]

Depends on / 依赖: arrow_tgt
-/
lemma arrow_tgt (f : Path X m) (i : Fin m) :
    X.map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ :=
  Path₁.arrow_tgt f i

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : Path X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow)
  proof: Path₁.ext hᵥ hₐ

中文:
引理 ext
  条件: {f g : 道路 X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow)
  证明: Path₁.ext hᵥ hₐ
-/
lemma ext {f g : Path X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  Path₁.ext hᵥ hₐ

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
/--
lemma `ext'` / 引理 `ext'`

English:
lemma ext'
  given: {f g : Path X (m + 1)} (h : forall i, f.arrow i = g.arrow i)
  statement: f = g
  proof: by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m)]; rw [← g.arrow_tgt (Fin.last m)]; rw [h]
  · exact h j

中文:
引理 ext'
  条件: {f g : 道路 X (m + 1)} (h : 对任意 i, f.arrow i = g.arrow i)
  结论: f = g
  证明: by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m)]; rw [← g.arrow_tgt (Fin.last m)]; rw [h]
  · exact h j

Depends on / 依赖: Fin.eq_castSucc_or_eq_last, Fin.last, Fin.succ_last, arrow_src, arrow_tgt, eq_castSucc_or_eq_last, f.arrow_src, f.arrow_tgt, g.arrow_src, g.arrow_tgt, succ_last
-/
lemma ext' {f g : Path X (m + 1)} (h : forall i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m)]; rw [← g.arrow_tgt (Fin.last m)]; rw [h]
  · exact h j

/-- Constructor for paths of length `2` from two paths of length `1`. -/
@[simps!]
/--
Definition of `mk₂` / `mk₂` 的定义

English:
definition mk₂
  signature: {n : Nat} {X : Truncated.{u} (n + 1)} (p q : X.Path 1)
  body: ![p.vertex 0, p.vertex 1, q.vertex 1]
  arrow := ![p.arrow 0, q.arrow 0]
  arrow_src i := by
    fin_cases i
    · exact p.arrow_src 0
    · exact (q.arrow_src 0).trans h.symm
  arrow_tgt i := by
    fin_cases i
    · exact p.arrow_tgt 0
    · exact q.arrow_tgt 0

中文:
定义 mk₂
  签名: {n : 自然数} {X : Truncated.{u} (n + 1)} (p q : X.道路 1)
  定义体: ![p.vertex 0, p.vertex 1, q.vertex 1]
  arrow := ![p.arrow 0, q.arrow 0]
  arrow_src i := by
    fin_cases i
    · exact p.arrow_src 0
    · exact (q.arrow_src 0).trans h.symm
  arrow_tgt i := by
    fin_cases i
    · exact p.arrow_tgt 0
    · exact q.arrow_tgt 0

Depends on / 依赖: p.vertex, q.vertex, vertex
-/
def mk₂ {n : Nat} {X : Truncated.{u} (n + 1)} (p q : X.Path 1)
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

/--
Definition of `interval` / `interval` 的定义

English:
definition interval
  signature: (f : Path X m) (j l : Nat) (h : j + l <= m := by omega)
  body: f.vertex ⟨j + i, by lia⟩
  arrow i := f.arrow ⟨j + i, by lia⟩
  arrow_src i := f.arrow_src ⟨j + i, by lia⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by lia⟩

中文:
定义 interval
  签名: (f : 道路 X m) (j l : 自然数) (h : j + l <= m := by omega)
  定义体: f.vertex ⟨j + i, by lia⟩
  arrow i := f.arrow ⟨j + i, by lia⟩
  arrow_src i := f.arrow_src ⟨j + i, by lia⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by lia⟩

Depends on / 依赖: arrow_src, arrow_tgt, f.arrow, f.arrow_src, f.arrow_tgt, f.vertex, vertex
-/
def interval (f : Path X m) (j l : Nat) (h : j + l <= m := by omega) : Path X l where
  vertex i := f.vertex ⟨j + i, by lia⟩
  arrow i := f.arrow ⟨j + i, by lia⟩
  arrow_src i := f.arrow_src ⟨j + i, by lia⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by lia⟩

variable {X Y : SSet.Truncated.{u} (n + 1)} {m : Nat}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Path X m) (σ : X ⟶ Y)
  body: σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i)
  arrow i := σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
.symm exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 1)).op) _
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
.symm exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 0)).op) _

中文:
定义 map
  签名: (f : 道路 X m) (σ : X ⟶ Y)
  定义体: σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i)
  arrow i := σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
.symm exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 1)).op) _
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
.symm exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 0)).op) _

Depends on / 依赖: f.vertex, vertex
-/
def map (f : Path X m) (σ : X ⟶ Y) : Path Y m where
  vertex i := σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i)
  arrow i := σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
.symm exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 1)).op) _
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
.symm exact ConcreteCategory.congr_hom (σ.naturality (tr (δ 0)).op) _

/- We write this lemma manually to ensure it refers to `Path.vertex`. -/
@[simp]
/--
lemma `map_vertex` / 引理 `map_vertex`

English:
lemma map_vertex
  given: (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1))
  proof: rfl

中文:
引理 map_vertex
  条件: (f : 道路 X m) (σ : X ⟶ Y) (i : 有限集 (m + 1))
  证明: rfl
-/
lemma map_vertex (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1)) :
    (f.map σ).vertex i = σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i) :=
  rfl

/- We write this lemma manually to ensure it refers to `Path.arrow`. -/
@[simp]
/--
lemma `map_arrow` / 引理 `map_arrow`

English:
lemma map_arrow
  given: (f : Path X m) (σ : X ⟶ Y) (i : Fin m)
  proof: rfl

中文:
引理 map_arrow
  条件: (f : 道路 X m) (σ : X ⟶ Y) (i : 有限集 m)
  证明: rfl
-/
lemma map_arrow (f : Path X m) (σ : X ⟶ Y) (i : Fin m) :
    (f.map σ).arrow i = σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i) :=
  rfl


/--
lemma `map_interval` / 引理 `map_interval`

English:
lemma map_interval
  given: (f : Path X m) (σ : X ⟶ Y) (j l : Nat) (h : j + l <= m)
  proof: rfl

中文:
引理 map_interval
  条件: (f : 道路 X m) (σ : X ⟶ Y) (j l : 自然数) (h : j + l <= m)
  证明: rfl
-/
lemma map_interval (f : Path X m) (σ : X ⟶ Y) (j l : Nat) (h : j + l <= m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

variable {n : Nat} (X : SSet.Truncated.{u} (n + 1))

/--
Definition of `spine` / `spine` 的定义

English:
definition spine
  signature: (m : Nat) (h : m <= n + 1 := by omega) (Δ : X _⦋m⦌ₙ₊₁)
  body: X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ
  arrow i := X.map (tr (mkOfSucc i)).op Δ
  arrow_src i := by
    simp [← δ_one_mkOfSucc, tr_comp]
    rfl
  arrow_tgt i := by
    simp [← δ_zero_mkOfSucc, tr_comp]
    rfl

中文:
定义 spine
  签名: (m : 自然数) (h : m <= n + 1 := by omega) (Δ : X _⦋m⦌ₙ₊₁)
  定义体: X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ
  arrow i := X.map (tr (mkOfSucc i)).op Δ
  arrow_src i := by
    simp [← δ_one_mkOfSucc, tr_comp]
    rfl
  arrow_tgt i := by
    simp [← δ_zero_mkOfSucc, tr_comp]
    rfl

Depends on / 依赖: SimplexCategory, SimplexCategory.const, X.map, arrow_src, arrow_tgt, mkOfSucc, tr_comp, vertex
-/
def spine (m : Nat) (h : m <= n + 1 := by omega) (Δ : X _⦋m⦌ₙ₊₁) : Path X m where
  vertex i := X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ
  arrow i := X.map (tr (mkOfSucc i)).op Δ
  arrow_src i := by
    simp [← δ_one_mkOfSucc, tr_comp]
    rfl
  arrow_tgt i := by
    simp [← δ_zero_mkOfSucc, tr_comp]
    rfl

/--
lemma `trunc_spine` / 引理 `trunc_spine`

English:
lemma trunc_spine
  given: (k m : Nat) (h : m <= k + 1) (hₙ : k <= n)
  proof: rfl

中文:
引理 trunc_spine
  条件: (k m : 自然数) (h : m <= k + 1) (hₙ : k <= n)
  证明: rfl
-/
lemma trunc_spine (k m : Nat) (h : m <= k + 1) (hₙ : k <= n) :
    ((trunc (n + 1) (k + 1)).obj X).spine m = X.spine m :=
  rfl

variable (m : Nat) (hₘ : m <= n + 1)

/- We write this lemma manually to ensure it refers to `Path.vertex`. -/
@[simp]
/--
lemma `spine_vertex` / 引理 `spine_vertex`

English:
lemma spine_vertex
  given: (Δ : X _⦋m⦌ₙ₊₁) (i : Fin (m + 1))
  proof: rfl

中文:
引理 spine_vertex
  条件: (Δ : X _⦋m⦌ₙ₊₁) (i : 有限集 (m + 1))
  证明: rfl
-/
lemma spine_vertex (Δ : X _⦋m⦌ₙ₊₁) (i : Fin (m + 1)) :
    (X.spine m hₘ Δ).vertex i =
      X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ :=
  rfl

/- We write this lemma manually to ensure it refers to `Path.arrow`. -/
@[simp]
/--
lemma `spine_arrow` / 引理 `spine_arrow`

English:
lemma spine_arrow
  given: (Δ : X _⦋m⦌ₙ₊₁) (i : Fin m)
  proof: rfl

中文:
引理 spine_arrow
  条件: (Δ : X _⦋m⦌ₙ₊₁) (i : 有限集 m)
  证明: rfl
-/
lemma spine_arrow (Δ : X _⦋m⦌ₙ₊₁) (i : Fin m) :
    (X.spine m hₘ Δ).arrow i = X.map (tr (mkOfSucc i)).op Δ :=
  rfl

/--
lemma `spine_map_vertex` / 引理 `spine_map_vertex`

English:
lemma spine_map_vertex
  statement: (Δ : X _⦋m⦌ₙ₊₁) (a : Nat) (hₐ : a <= n + 1)
  proof: by
  dsimp only [spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp']; rw [SimplexCategory.const_comp]

中文:
引理 spine_map_vertex
  结论: (Δ : X _⦋m⦌ₙ₊₁) (a : 自然数) (hₐ : a <= n + 1)
  证明: by
  dsimp only [spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp']; rw [SimplexCategory.const_comp]

Depends on / 依赖: Functor, Functor.map_comp_apply, SimplexCategory, SimplexCategory.const_comp, const_comp, map_comp_apply, op_comp, spine_vertex, tr_comp
-/
lemma spine_map_vertex (Δ : X _⦋m⦌ₙ₊₁) (a : Nat) (hₐ : a <= n + 1)
    (φ : ⦋a⦌ₙ₊₁ ⟶ ⦋m⦌ₙ₊₁) (i : Fin (a + 1)) :
    (X.spine a hₐ (X.map φ.op Δ)).vertex i =
      (X.spine m hₘ Δ).vertex (φ.hom.toOrderHom i) := by
  dsimp only [spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp']; rw [SimplexCategory.const_comp]

/--
lemma `spine_map_subinterval` / 引理 `spine_map_subinterval`

English:
lemma spine_map_subinterval
  given: (j l : Nat) (h : j + l <= m) (Δ : X _⦋m⦌ₙ₊₁)
  proof: by
  ext i
  · dsimp only [spine_vertex, Path.interval]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [const_subinterval_eq]
  · dsimp only [spine_arrow, Path.interval]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_subinterval_eq]

中文:
引理 spine_map_subinterval
  条件: (j l : 自然数) (h : j + l <= m) (Δ : X _⦋m⦌ₙ₊₁)
  证明: by
  ext i
  · dsimp only [spine_vertex, Path.interval]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [const_subinterval_eq]
  · dsimp only [spine_arrow, Path.interval]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_subinterval_eq]

Depends on / 依赖: Functor, Functor.map_comp_apply, Path.interval, const_subinterval_eq, interval, map_comp_apply, mkOfSucc_subinterval_eq, op_comp, spine_arrow, spine_vertex, tr_comp
-/
lemma spine_map_subinterval (j l : Nat) (h : j + l <= m) (Δ : X _⦋m⦌ₙ₊₁) :
    X.spine l (by lia) (X.map (tr (subinterval j l h)).op Δ) =
      (X.spine m hₘ Δ).interval j l h := by
  ext i
  · dsimp only [spine_vertex, Path.interval]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [const_subinterval_eq]
  · dsimp only [spine_arrow, Path.interval]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_subinterval_eq]

end Truncated

/-- A path of length `n` in a simplicial set `X` is defined as a 1-truncated
path in the 1-truncation of `X`. -/
.Path n .obj X abbrev Path (X : SSet.{u}) (n : Nat) := truncation 1

namespace Path

variable {X : SSet.{u}} {n : Nat}

/--
Definition of `vertex` / `vertex` 的定义

English:
abbreviation vertex
  signature: (f : Path X n) (i : Fin (n + 1))
  body: Truncated.Path.vertex f i

中文:
缩写 vertex
  签名: (f : 道路 X n) (i : 有限集 (n + 1))
  定义体: Truncated.Path.vertex f i

Depends on / 依赖: Truncated, Truncated.Path.vertex, vertex
-/
abbrev vertex (f : Path X n) (i : Fin (n + 1)) : X _⦋0⦌ :=
  Truncated.Path.vertex f i

/--
Definition of `arrow` / `arrow` 的定义

English:
abbreviation arrow
  signature: (f : Path X n) (i : Fin n)
  body: Truncated.Path.arrow f i

中文:
缩写 arrow
  签名: (f : 道路 X n) (i : 有限集 n)
  定义体: Truncated.Path.arrow f i

Depends on / 依赖: Truncated, Truncated.Path.arrow
-/
abbrev arrow (f : Path X n) (i : Fin n) : X _⦋1⦌ :=
  Truncated.Path.arrow f i

/--
lemma `congr_vertex` / 引理 `congr_vertex`

English:
lemma congr_vertex
  given: {f g : Path X n} (h : f = g) (i : Fin (n + 1))
  proof: by rw [h]

中文:
引理 congr_vertex
  条件: {f g : 道路 X n} (h : f = g) (i : 有限集 (n + 1))
  证明: by rw [h]
-/
lemma congr_vertex {f g : Path X n} (h : f = g) (i : Fin (n + 1)) :
    f.vertex i = g.vertex i := by rw [h]

/--
lemma `congr_arrow` / 引理 `congr_arrow`

English:
lemma congr_arrow
  given: {f g : Path X n} (h : f = g) (i : Fin n)
  proof: by rw [h]

中文:
引理 congr_arrow
  条件: {f g : 道路 X n} (h : f = g) (i : 有限集 n)
  证明: by rw [h]
-/
lemma congr_arrow {f g : Path X n} (h : f = g) (i : Fin n) :
    f.arrow i = g.arrow i := by rw [h]

/--
lemma `arrow_src` / 引理 `arrow_src`

English:
lemma arrow_src
  given: (f : Path X n) (i : Fin n)
  proof: Truncated.Path.arrow_src f i

中文:
引理 arrow_src
  条件: (f : 道路 X n) (i : 有限集 n)
  证明: Truncated.Path.arrow_src f i

Depends on / 依赖: Truncated, Truncated.Path.arrow_src, arrow_src
-/
lemma arrow_src (f : Path X n) (i : Fin n) :
    X.δ 1 (f.arrow i) = f.vertex i.castSucc :=
  Truncated.Path.arrow_src f i

/--
lemma `arrow_tgt` / 引理 `arrow_tgt`

English:
lemma arrow_tgt
  given: (f : Path X n) (i : Fin n)
  proof: Truncated.Path.arrow_tgt f i

@[ext]

中文:
引理 arrow_tgt
  条件: (f : 道路 X n) (i : 有限集 n)
  证明: Truncated.Path.arrow_tgt f i

@[ext]

Depends on / 依赖: Truncated, Truncated.Path.arrow_tgt, arrow_tgt
-/
lemma arrow_tgt (f : Path X n) (i : Fin n) :
    X.δ 0 (f.arrow i) = f.vertex i.succ :=
  Truncated.Path.arrow_tgt f i

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow)
  proof: Truncated.Path.ext hᵥ hₐ

中文:
引理 ext
  条件: {f g : 道路 X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow)
  证明: Truncated.Path.ext hᵥ hₐ

Depends on / 依赖: Truncated, Truncated.Path.ext
-/
lemma ext {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  Truncated.Path.ext hᵥ hₐ

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
/--
lemma `ext'` / 引理 `ext'`

English:
lemma ext'
  given: {f g : Path X (n + 1)} (h : forall i, f.arrow i = g.arrow i)
  statement: f = g
  proof: Truncated.Path.ext' h

@[ext]

中文:
引理 ext'
  条件: {f g : 道路 X (n + 1)} (h : 对任意 i, f.arrow i = g.arrow i)
  结论: f = g
  证明: Truncated.Path.ext' h

@[ext]

Depends on / 依赖: Truncated, Truncated.Path.ext
-/
lemma ext' {f g : Path X (n + 1)} (h : forall i, f.arrow i = g.arrow i) : f = g :=
  Truncated.Path.ext' h

@[ext]
/--
lemma `ext₀` / 引理 `ext₀`

English:
lemma ext₀
  given: {f g : Path X 0} (h : f.vertex 0 = g.vertex 0)
  statement: f = g
  proof: by
  ext i
  · fin_cases i; exact h
  · fin_cases i

中文:
引理 ext₀
  条件: {f g : 道路 X 0} (h : f.vertex 0 = g.vertex 0)
  结论: f = g
  证明: by
  ext i
  · fin_cases i; exact h
  · fin_cases i

Depends on / 依赖: fin_cases
-/
lemma ext₀ {f g : Path X 0} (h : f.vertex 0 = g.vertex 0) : f = g := by
  ext i
  · fin_cases i; exact h
  · fin_cases i

/--
Definition of `interval` / `interval` 的定义

English:
definition interval
  signature: (f : Path X n) (j l : Nat) (h : j + l <= n := by grind)
  body: Truncated.Path.interval f j l h

中文:
定义 interval
  签名: (f : 道路 X n) (j l : 自然数) (h : j + l <= n := by grind)
  定义体: Truncated.Path.interval f j l h

Depends on / 依赖: Truncated, Truncated.Path.interval, interval
-/
def interval (f : Path X n) (j l : Nat) (h : j + l <= n := by grind) : Path X l :=
  Truncated.Path.interval f j l h

/--
lemma `arrow_interval` / 引理 `arrow_interval`

English:
lemma arrow_interval
  statement: (f : Path X n) (j l : Nat) (k' : Fin l) (k : Fin n)
  proof: by
  dsimp [interval, arrow, Truncated.Path.interval, Truncated.Path.arrow]
  congr

中文:
引理 arrow_interval
  结论: (f : 道路 X n) (j l : 自然数) (k' : 有限集 l) (k : 有限集 n)
  证明: by
  dsimp [interval, arrow, Truncated.Path.interval, Truncated.Path.arrow]
  congr

Depends on / 依赖: Truncated, Truncated.Path.arrow, Truncated.Path.interval, f.arrow, f.interval, interval
-/
lemma arrow_interval (f : Path X n) (j l : Nat) (k' : Fin l) (k : Fin n)
    (h : j + l <= n := by lia) (hkk' : j + k' = k := by grind) :
    (f.interval j l h).arrow k' = f.arrow k := by
  dsimp [interval, arrow, Truncated.Path.interval, Truncated.Path.arrow]
  congr

variable {X Y : SSet.{u}} {n : Nat}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Path X n) (σ : X ⟶ Y)
  body: Truncated.Path.map f ((truncation 1).map σ)

@[simp]

中文:
定义 map
  签名: (f : 道路 X n) (σ : X ⟶ Y)
  定义体: Truncated.Path.map f ((truncation 1).map σ)

@[simp]

Depends on / 依赖: Truncated, Truncated.Path.map, truncation
-/
def map (f : Path X n) (σ : X ⟶ Y) : Path Y n :=
  Truncated.Path.map f ((truncation 1).map σ)

@[simp]
/--
lemma `map_vertex` / 引理 `map_vertex`

English:
lemma map_vertex
  given: (f : Path X n) (σ : X ⟶ Y) (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 map_vertex
  条件: (f : 道路 X n) (σ : X ⟶ Y) (i : 有限集 (n + 1))
  证明: rfl

@[simp]
-/
lemma map_vertex (f : Path X n) (σ : X ⟶ Y) (i : Fin (n + 1)) :
    (f.map σ).vertex i = σ.app (op ⦋0⦌) (f.vertex i) :=
  rfl

@[simp]
/--
lemma `map_arrow` / 引理 `map_arrow`

English:
lemma map_arrow
  given: (f : Path X n) (σ : X ⟶ Y) (i : Fin n)
  proof: rfl

中文:
引理 map_arrow
  条件: (f : 道路 X n) (σ : X ⟶ Y) (i : 有限集 n)
  证明: rfl
-/
lemma map_arrow (f : Path X n) (σ : X ⟶ Y) (i : Fin n) :
    (f.map σ).arrow i = σ.app (op ⦋1⦌) (f.arrow i) :=
  rfl

/--
lemma `map_interval` / 引理 `map_interval`

English:
lemma map_interval
  given: (f : Path X n) (σ : X ⟶ Y) (j l : Nat) (h : j + l <= n)
  proof: rfl

中文:
引理 map_interval
  条件: (f : 道路 X n) (σ : X ⟶ Y) (j l : 自然数) (h : j + l <= n)
  证明: rfl
-/
lemma map_interval (f : Path X n) (σ : X ⟶ Y) (j l : Nat) (h : j + l <= n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

section spine

variable (X : SSet.{u}) (n : Nat)

/--
Definition of `spine` / `spine` 的定义

English:
definition spine
  signature: : X _⦋n⦌ -> Path X n
  body: .spine n .obj X truncation (n + 1)

@[simp]

中文:
定义 spine
  签名: : X _⦋n⦌ -> 道路 X n
  定义体: .spine n .obj X truncation (n + 1)

@[simp]

Depends on / 依赖: truncation
-/
def spine : X _⦋n⦌ -> Path X n :=
.spine n .obj X truncation (n + 1)

@[simp]
/--
lemma `spine_vertex` / 引理 `spine_vertex`

English:
lemma spine_vertex
  given: (Δ : X _⦋n⦌) (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 spine_vertex
  条件: (Δ : X _⦋n⦌) (i : 有限集 (n + 1))
  证明: rfl

@[simp]
-/
lemma spine_vertex (Δ : X _⦋n⦌) (i : Fin (n + 1)) :
    (X.spine n Δ).vertex i = X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op Δ :=
  rfl

@[simp]
/--
lemma `spine_arrow` / 引理 `spine_arrow`

English:
lemma spine_arrow
  given: (Δ : X _⦋n⦌) (i : Fin n)
  proof: rfl

中文:
引理 spine_arrow
  条件: (Δ : X _⦋n⦌) (i : 有限集 n)
  证明: rfl
-/
lemma spine_arrow (Δ : X _⦋n⦌) (i : Fin n) :
    (X.spine n Δ).arrow i = X.map (mkOfSucc i).op Δ :=
  rfl

/--
lemma `spine_δ₀` / 引理 `spine_δ₀`

English:
lemma spine_δ₀
  given: {m : Nat} (x : X _⦋m + 1⦌)
  proof: by
  obtain _ | m := m
  · ext
    simp [spine, Path.vertex, Truncated.Path.vertex,
      Truncated.spine, Path.interval, Truncated.Path.interval,
      Truncated.Hom.tr, ← SimplexCategory.δ_zero_eq_const]
    rfl
  · ext i
    dsimp
    rw [SimplicialObject.δ_def]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp)]
    symm
    exact Path.arrow_interval _ _ _ _ _ _ (by rw [Fin.val_succ, add_comm])

中文:
引理 spine_δ₀
  条件: {m : 自然数} (x : X _⦋m + 1⦌)
  证明: by
  obtain _ | m := m
  · ext
    simp [spine, Path.vertex, Truncated.Path.vertex,
      Truncated.spine, Path.interval, Truncated.Path.interval,
      Truncated.Hom.tr, ← SimplexCategory.δ_zero_eq_const]
    rfl
  · ext i
    dsimp
    rw [SimplicialObject.δ_def]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp)]
    symm
    exact Path.arrow_interval _ _ _ _ _ _ (by rw [Fin.val_succ, add_comm])

Depends on / 依赖: Fin.val_succ, Functor, Functor.map_comp_apply, Path.arrow_interval, Path.interval, Path.vertex, SimplexCategory, SimplexCategory.mkOfSucc_, SimplicialObject, Truncated, Truncated.Hom.tr, Truncated.Path.interval, Truncated.Path.vertex, Truncated.spine, add_comm, arrow_interval, interval, map_comp_apply, op_comp, val_succ
-/
lemma spine_δ₀ {m : Nat} (x : X _⦋m + 1⦌) :
    X.spine m (X.δ 0 x) = (X.spine (m + 1) x).interval 1 m := by
  obtain _ | m := m
  · ext
    simp [spine, Path.vertex, Truncated.Path.vertex,
      Truncated.spine, Path.interval, Truncated.Path.interval,
      Truncated.Hom.tr, ← SimplexCategory.δ_zero_eq_const]
    rfl
  · ext i
    dsimp
    rw [SimplicialObject.δ_def]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp)]
    symm
    exact Path.arrow_interval _ _ _ _ _ _ (by rw [Fin.val_succ, add_comm])

/--
lemma `truncation_spine` / 引理 `truncation_spine`

English:
lemma truncation_spine
  given: (m : Nat) (h : m <= n + 1)
  proof: rfl

中文:
引理 truncation_spine
  条件: (m : 自然数) (h : m <= n + 1)
  证明: rfl
-/
lemma truncation_spine (m : Nat) (h : m <= n + 1) :
    ((truncation (n + 1)).obj X).spine m = X.spine m :=
  rfl

/--
lemma `spine_map_vertex` / 引理 `spine_map_vertex`

English:
lemma spine_map_vertex
  statement: (Δ : X _⦋n⦌) {m : Nat}
  proof: .obj X truncation (max m n + 1)
.spine_map_vertex n (by omega) Δ m (by omega) (InducedCategory.homMk φ) i

中文:
引理 spine_map_vertex
  结论: (Δ : X _⦋n⦌) {m : 自然数}
  证明: .obj X truncation (max m n + 1)
.spine_map_vertex n (by omega) Δ m (by omega) (InducedCategory.homMk φ) i

Depends on / 依赖: InducedCategory, InducedCategory.homMk, spine_map_vertex, truncation
-/
lemma spine_map_vertex (Δ : X _⦋n⦌) {m : Nat}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (X.spine m (X.map φ.op Δ)).vertex i =
      (X.spine n Δ).vertex (φ.toOrderHom i) :=
.obj X truncation (max m n + 1)
.spine_map_vertex n (by omega) Δ m (by omega) (InducedCategory.homMk φ) i

/--
lemma `spine_map_subinterval` / 引理 `spine_map_subinterval`

English:
lemma spine_map_subinterval
  given: (j l : Nat) (h : j + l <= n) (Δ : X _⦋n⦌)
  proof: .spine_map_subinterval n (by lia) j l h Δ .obj X truncation (n + 1)

中文:
引理 spine_map_subinterval
  条件: (j l : 自然数) (h : j + l <= n) (Δ : X _⦋n⦌)
  证明: .spine_map_subinterval n (by lia) j l h Δ .obj X truncation (n + 1)

Depends on / 依赖: spine_map_subinterval, truncation
-/
lemma spine_map_subinterval (j l : Nat) (h : j + l <= n) (Δ : X _⦋n⦌) :
    X.spine l (X.map (subinterval j l h).op Δ) = (X.spine n Δ).interval j l h :=
.spine_map_subinterval n (by lia) j l h Δ .obj X truncation (n + 1)

end spine

/--
Definition of `stdSimplex.spineId` / `stdSimplex.spineId` 的定义

English:
definition stdSimplex.spineId
  signature: (n : Nat)
  body: spine Δ[n] n (objEquiv.symm (𝟙 _))

@[simp]

中文:
定义 stdSimplex.spineId
  签名: (n : 自然数)
  定义体: spine Δ[n] n (objEquiv.symm (𝟙 _))

@[simp]

Depends on / 依赖: objEquiv, objEquiv.symm
-/
def stdSimplex.spineId (n : Nat) : Path Δ[n] n :=
  spine Δ[n] n (objEquiv.symm (𝟙 _))

@[simp]
/--
lemma `stdSimplex.spineId_vertex` / 引理 `stdSimplex.spineId_vertex`

English:
lemma stdSimplex.spineId_vertex
  given: (n : Nat) (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 stdSimplex.spineId_vertex
  条件: (n : 自然数) (i : 有限集 (n + 1))
  证明: rfl

@[simp]
-/
lemma stdSimplex.spineId_vertex (n : Nat) (i : Fin (n + 1)) :
    (stdSimplex.spineId n).vertex i = obj₀Equiv.symm i := rfl

@[simp]
/--
lemma `stdSimplex.spineId_arrow_apply_zero` / 引理 `stdSimplex.spineId_arrow_apply_zero`

English:
lemma stdSimplex.spineId_arrow_apply_zero
  given: (n : Nat) (i : Fin n)
  proof: rfl

@[simp]

中文:
引理 stdSimplex.spineId_arrow_apply_zero
  条件: (n : 自然数) (i : 有限集 n)
  证明: rfl

@[simp]
-/
lemma stdSimplex.spineId_arrow_apply_zero (n : Nat) (i : Fin n) :
    (stdSimplex.spineId n).arrow i 0 = i.castSucc := rfl

@[simp]
/--
lemma `stdSimplex.spineId_arrow_apply_one` / 引理 `stdSimplex.spineId_arrow_apply_one`

English:
lemma stdSimplex.spineId_arrow_apply_one
  given: (n : Nat) (i : Fin n)
  proof: rfl

中文:
引理 stdSimplex.spineId_arrow_apply_one
  条件: (n : 自然数) (i : 有限集 n)
  证明: rfl
-/
lemma stdSimplex.spineId_arrow_apply_one (n : Nat) (i : Fin n) :
    (stdSimplex.spineId n).arrow i 1 = i.succ := rfl

/-- A path of a simplicial set can be lifted to a subcomplex if the vertices
and arrows belong to this subcomplex. -/
@[simps]
/--
Definition of `Subcomplex.liftPath` / `Subcomplex.liftPath` 的定义

English:
definition Subcomplex.liftPath
  signature: {X : SSet.{u}} (A : X.Subcomplex) {n : Nat} (p : Path X n)
  body: ⟨p.vertex j, hp₀ _⟩
  arrow j := ⟨p.arrow j, hp₁ _⟩
arrow_src j := Subtype.ext p.arrow_src j
arrow_tgt j := Subtype.ext p.arrow_tgt j

@[simp]

中文:
定义 子复形.liftPath
  签名: {X : SSet.{u}} (A : X.子复形) {n : 自然数} (p : 道路 X n)
  定义体: ⟨p.vertex j, hp₀ _⟩
  arrow j := ⟨p.arrow j, hp₁ _⟩
arrow_src j := Subtype.ext p.arrow_src j
arrow_tgt j := Subtype.ext p.arrow_tgt j

@[simp]

Depends on / 依赖: p.vertex, vertex
-/
def Subcomplex.liftPath {X : SSet.{u}} (A : X.Subcomplex) {n : Nat} (p : Path X n)
    (hp₀ : forall j, p.vertex j in A.obj _)
    (hp₁ : forall j, p.arrow j in A.obj _) :
    Path A n where
  vertex j := ⟨p.vertex j, hp₀ _⟩
  arrow j := ⟨p.arrow j, hp₁ _⟩
arrow_src j := Subtype.ext p.arrow_src j
arrow_tgt j := Subtype.ext p.arrow_tgt j

@[simp]
/--
lemma `Subcomplex.map_ι_liftPath` / 引理 `Subcomplex.map_ι_liftPath`

English:
lemma Subcomplex.map_ι_liftPath
  statement: {X : SSet.{u}} (A : X.Subcomplex) {n : Nat} (p : Path X n)
  proof: rfl

中文:
引理 子复形.map_ι_liftPath
  结论: {X : SSet.{u}} (A : X.子复形) {n : 自然数} (p : 道路 X n)
  证明: rfl
-/
lemma Subcomplex.map_ι_liftPath {X : SSet.{u}} (A : X.Subcomplex) {n : Nat} (p : Path X n)
    (hp₀ : forall j, p.vertex j in A.obj _)
    (hp₁ : forall j, p.arrow j in A.obj _) :
    (A.liftPath p hp₀ hp₁).map A.ι = p := rfl

/-- Any inner horn contains the spine of the unique non-degenerate `n`-simplex
in `Δ[n]`. -/
@[simps! vertex_coe arrow_coe]
/--
Definition of `horn.spineId` / `horn.spineId` 的定义

English:
definition horn.spineId
  signature: {n : Nat} (i : Fin (n + 3))
  body: Λ[n + 2, i].liftPath (stdSimplex.spineId (n + 2)) (by simp) (fun j => by
    convert! (horn.primitiveEdge.{u} h₀ hₙ j).2
    ext a
    fin_cases a <;> rfl)

@[simp]

中文:
定义 horn.spineId
  签名: {n : 自然数} (i : 有限集 (n + 3))
  定义体: Λ[n + 2, i].liftPath (stdSimplex.spineId (n + 2)) (by simp) (fun j => by
    convert! (horn.primitiveEdge.{u} h₀ hₙ j).2
    ext a
    fin_cases a <;> rfl)

@[simp]

Depends on / 依赖: convert, fin_cases, horn.primitiveEdge, liftPath, primitiveEdge, spineId, stdSimplex, stdSimplex.spineId
-/
def horn.spineId {n : Nat} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path (Λ[n + 2, i] : SSet.{u}) (n + 2) :=
  Λ[n + 2, i].liftPath (stdSimplex.spineId (n + 2)) (by simp) (fun j => by
    convert! (horn.primitiveEdge.{u} h₀ hₙ j).2
    ext a
    fin_cases a <;> rfl)

@[simp]
/--
lemma `horn.spineId_map_hornInclusion` / 引理 `horn.spineId_map_hornInclusion`

English:
lemma horn.spineId_map_hornInclusion
  statement: {n : Nat} (i : Fin (n + 3))
  proof: rfl

中文:
引理 horn.spineId_map_hornInclusion
  结论: {n : 自然数} (i : 有限集 (n + 3))
  证明: rfl
-/
lemma horn.spineId_map_hornInclusion {n : Nat} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path.map (horn.spineId.{u} i h₀ hₙ) Λ[n + 2, i].ι =
      stdSimplex.spineId (n + 2) := rfl

end SSet
