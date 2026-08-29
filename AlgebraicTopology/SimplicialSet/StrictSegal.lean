/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Path

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _⦋n⦌ → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

open Opposite SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

variable {n : Nat} (X : SSet.Truncated.{u} (n + 1))

/--
Definition of `StrictSegal` / `StrictSegal` 的定义

English:
structure StrictSegal
  parameters: where
  axioms and operations (3):
    - spineToSimplex((m : Nat) (h : m <= n + 1 := by lia)) : Path X m -> X _⦋m⦌ₙ₊₁
    - spine_spineToSimplex((m : Nat) (h : m <= n + 1)) : spine X m ∘ spineToSimplex m = id
    - spineToSimplex_spine((m : Nat) (h : m <= n + 1)) : spineToSimplex m ∘ spine X m = id

中文:
结构 StrictSegal
  参数: where
  公理与运算 (3 个):
    - spineToSimplex((m : 自然数) (h : m <= n + 1 := by lia)) : Path X m -> X _⦋m⦌ₙ₊₁
    - spine_spineToSimplex((m : 自然数) (h : m <= n + 1)) : spine X m ∘ spineToSimplex m = id
    - spineToSimplex_spine((m : 自然数) (h : m <= n + 1)) : spineToSimplex m ∘ spine X m = id
-/
structure StrictSegal where
  /-- The inverse to `spine X m`. -/
  spineToSimplex (m : Nat) (h : m <= n + 1 := by lia) : Path X m -> X _⦋m⦌ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : Nat) (h : m <= n + 1) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : Nat) (h : m <= n + 1) :
    spineToSimplex m ∘ spine X m = id

/--
Definition of `IsStrictSegal` / `IsStrictSegal` 的定义

English:
class IsStrictSegal
  parameters: (X : SSet.Truncated.{u} (n + 1))
  axioms and operations (1):
    - spine_bijective((X) (m : Nat) (h : m <= n + 1 := by grind)) : Function.Bijective (X.spine m)

中文:
类 IsStrictSegal
  参数: (X : SSet.Truncated.{u} (n + 1))
  公理与运算 (1 个):
    - spine_bijective((X) (m : 自然数) (h : m <= n + 1 := by grind)) : Function.Bijective (X.spine m)

Depends on / 依赖: Bijective, Function, Function.Bijective, X.spine
-/
class IsStrictSegal (X : SSet.Truncated.{u} (n + 1)) : Prop where
  spine_bijective (X) (m : Nat) (h : m <= n + 1 := by grind) : Function.Bijective (X.spine m)

export IsStrictSegal (spine_bijective)

/--
lemma `spine_injective` / 引理 `spine_injective`

English:
lemma spine_injective
  statement: (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
  proof: (spine_bijective X m).injective

中文:
引理 spine_injective
  结论: (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
  证明: (spine_bijective X m).injective

Depends on / 依赖: injective, spine_bijective
-/
lemma spine_injective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
    {m : Nat} {h : m <= n + 1} :
    Function.Injective (X.spine m) :=
  (spine_bijective X m).injective

/--
lemma `spine_surjective` / 引理 `spine_surjective`

English:
lemma spine_surjective
  statement: (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
  proof: (spine_bijective X m).surjective p

中文:
引理 spine_surjective
  结论: (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
  证明: (spine_bijective X m).surjective p

Depends on / 依赖: X.spine, spine_bijective, surjective
-/
lemma spine_surjective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
    {m : Nat} (p : X.Path m) (h : m <= n + 1 := by grind) :
    exists (x : X _⦋m⦌ₙ₊₁), X.spine m _ x = p :=
  (spine_bijective X m).surjective p

variable {X} in
/--
lemma `IsStrictSegal.ext` / 引理 `IsStrictSegal.ext`

English:
lemma IsStrictSegal.ext
  statement: [X.IsStrictSegal] {d : Nat} {hd} {x y : X _⦋d + 1⦌ₙ₊₁}
  proof: X.spine_injective (by ext i; apply h)

中文:
引理 IsStrictSegal.ext
  结论: [X.IsStrictSegal] {d : 自然数} {hd} {x y : X _⦋d + 1⦌ₙ₊₁}
  证明: X.spine_injective (by ext i; apply h)

Depends on / 依赖: X.spine_injective, spine_injective
-/
lemma IsStrictSegal.ext [X.IsStrictSegal] {d : Nat} {hd} {x y : X _⦋d + 1⦌ₙ₊₁}
    (h : forall (i : Fin (d + 1)),
      X.map (SimplexCategory.Truncated.Hom.tr (mkOfSucc i)).op x =
        X.map (SimplexCategory.Truncated.Hom.tr (mkOfSucc i)).op y) :
    x = y :=
  X.spine_injective (by ext i; apply h)

variable {X} in
/--
lemma `IsStrictSegal.hom_ext` / 引理 `IsStrictSegal.hom_ext`

English:
lemma IsStrictSegal.hom_ext
  statement: {Y : SSet.Truncated.{u} (n + 1)} [Y.IsStrictSegal]
  proof: by
  ext ⟨⟨m, hm⟩⟩ x
  induction m using SimplexCategory.rec with | _ m
  obtain _ | m := m
  · have fac := δ_comp_σ_self (i := (0 : Fin 1))
    dsimp at fac
    simpa [← NatTrans.naturality_apply,
      ← Functor.map_comp_apply, ← op_comp,
      ← SimplexCategory.Truncated.Hom.tr_comp, fac] using
 

中文:
引理 IsStrictSegal.hom_ext
  结论: {Y : SSet.Truncated.{u} (n + 1)} [Y.IsStrictSegal]
  证明: by
  ext ⟨⟨m, hm⟩⟩ x
  induction m using SimplexCategory.rec with | _ m
  obtain _ | m := m
  · have fac := δ_comp_σ_self (i := (0 : Fin 1))
    dsimp at fac
    simpa [← NatTrans.naturality_apply,
      ← Functor.map_comp_apply, ← op_comp,
      ← SimplexCategory.Truncated.Hom.tr_comp, fac] using
 

Depends on / 依赖: Functor, Functor.map_comp_apply, IsStrictSegal, IsStrictSegal.ext, NatTrans, NatTrans.naturality_apply, SimplexCategory, SimplexCategory.Truncated.Hom.tr, SimplexCategory.Truncated.Hom.tr_comp, SimplexCategory.rec, Truncated, X.map, Y.map, congr_arg, map_comp_apply, naturality_apply, op_comp, tr_comp
-/
lemma IsStrictSegal.hom_ext {Y : SSet.Truncated.{u} (n + 1)} [Y.IsStrictSegal]
    {f g : X ⟶ Y} (h : forall (x : X _⦋1⦌ₙ₊₁), f.app _ x = g.app _ x) : f = g := by
  ext ⟨⟨m, hm⟩⟩ x
  induction m using SimplexCategory.rec with | _ m
  obtain _ | m := m
  · have fac := δ_comp_σ_self (i := (0 : Fin 1))
    dsimp at fac
    simpa [← NatTrans.naturality_apply,
      ← Functor.map_comp_apply, ← op_comp,
      ← SimplexCategory.Truncated.Hom.tr_comp, fac] using
      congr_arg (Y.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ 0)).op)
        (h (X.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ 0)).op x))
  · exact IsStrictSegal.ext (fun i => by simp [← NatTrans.naturality_apply, h])

namespace StrictSegal

/--
Definition of `ofIsStrictSegal` / `ofIsStrictSegal` 的定义

English:
definition ofIsStrictSegal
  signature: [IsStrictSegal X]
  body: .invFun Equiv.ofBijective (X.spine m) (X.spine_bijective m h)
  spine_spineToSimplex m _ :=
funext .right_inv Equiv.ofBijective (X.spine m) _
  spineToSimplex_spine m _ :=
funext .left_inv Equiv.ofBijective (X.spine m) _

中文:
定义 ofIsStrictSegal
  签名: [IsStrictSegal X]
  定义体: .invFun Equiv.ofBijective (X.spine m) (X.spine_bijective m h)
  spine_spineToSimplex m _ :=
funext .right_inv Equiv.ofBijective (X.spine m) _
  spineToSimplex_spine m _ :=
funext .left_inv Equiv.ofBijective (X.spine m) _

Depends on / 依赖: Equiv.ofBijective, X.spine, X.spine_bijective, invFun, left_inv, ofBijective, right_inv, spineToSimplex_spine, spine_bijective, spine_spineToSimplex
-/
noncomputable def ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where
  spineToSimplex m h :=
.invFun Equiv.ofBijective (X.spine m) (X.spine_bijective m h)
  spine_spineToSimplex m _ :=
funext .right_inv Equiv.ofBijective (X.spine m) _
  spineToSimplex_spine m _ :=
funext .left_inv Equiv.ofBijective (X.spine m) _

variable {X} (sx : StrictSegal X)

section spineToSimplex

@[simp]
/--
lemma `spine_spineToSimplex_apply` / 引理 `spine_spineToSimplex_apply`

English:
lemma spine_spineToSimplex_apply
  given: (m : Nat) (h : m <= n + 1) (f : Path X m)
  proof: congr_fun (sx.spine_spineToSimplex m h) f

@[simp]

中文:
引理 spine_spineToSimplex_apply
  条件: (m : 自然数) (h : m <= n + 1) (f : Path X m)
  证明: congr_fun (sx.spine_spineToSimplex m h) f

@[simp]

Depends on / 依赖: congr_fun, spine_spineToSimplex, sx.spine_spineToSimplex
-/
lemma spine_spineToSimplex_apply (m : Nat) (h : m <= n + 1) (f : Path X m) :
    X.spine m h (sx.spineToSimplex m h f) = f :=
  congr_fun (sx.spine_spineToSimplex m h) f

@[simp]
/--
lemma `spineToSimplex_spine_apply` / 引理 `spineToSimplex_spine_apply`

English:
lemma spineToSimplex_spine_apply
  given: (m : Nat) (h : m <= n + 1) (Δ : X _⦋m⦌ₙ₊₁)
  proof: congr_fun (sx.spineToSimplex_spine m h) Δ

中文:
引理 spineToSimplex_spine_apply
  条件: (m : 自然数) (h : m <= n + 1) (Δ : X _⦋m⦌ₙ₊₁)
  证明: congr_fun (sx.spineToSimplex_spine m h) Δ

Depends on / 依赖: congr_fun, spineToSimplex_spine, sx.spineToSimplex_spine
-/
lemma spineToSimplex_spine_apply (m : Nat) (h : m <= n + 1) (Δ : X _⦋m⦌ₙ₊₁) :
    sx.spineToSimplex m h (X.spine m h Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine m h) Δ

section autoParam

variable (m : Nat) (h : m <= n + 1 := by lia)

set_option backward.privateInPublic true in
/--
Definition of `spineEquiv` / `spineEquiv` 的定义

English:
definition spineEquiv
  signature: : X _⦋m⦌ₙ₊₁ ≃ Path X m where
  body: X.spine m
  invFun := sx.spineToSimplex m h
  left_inv := sx.spineToSimplex_spine_apply m h
  right_inv := sx.spine_spineToSimplex_apply m h

中文:
定义 spineEquiv
  签名: : X _⦋m⦌ₙ₊₁ ≃ Path X m where
  定义体: X.spine m
  invFun := sx.spineToSimplex m h
  left_inv := sx.spineToSimplex_spine_apply m h
  right_inv := sx.spine_spineToSimplex_apply m h

Depends on / 依赖: X.spine
-/
def spineEquiv : X _⦋m⦌ₙ₊₁ ≃ Path X m where
  toFun := X.spine m
  invFun := sx.spineToSimplex m h
  left_inv := sx.spineToSimplex_spine_apply m h
  right_inv := sx.spine_spineToSimplex_apply m h

set_option backward.privateInPublic true in
/--
theorem `spineInjective` / 定理 `spineInjective`

English:
theorem spineInjective
  statement: Function.Injective (sx.spineEquiv m h)
  proof: Equiv.injective _

中文:
定理 spineInjective
  结论: Function.Injective (sx.spineEquiv m h)
  证明: Equiv.injective _

Depends on / 依赖: Equiv.injective, injective
-/
theorem spineInjective : Function.Injective (sx.spineEquiv m h) :=
  Equiv.injective _

set_option backward.privateInPublic true in
/--
Definition of `spineToDiagonal` / `spineToDiagonal` 的定义

English:
definition spineToDiagonal
  signature: : Path X m -> X _⦋1⦌ₙ₊₁
  body: X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

中文:
定义 spineToDiagonal
  签名: : Path X m -> X _⦋1⦌ₙ₊₁
  定义体: X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

Depends on / 依赖: X.map, spineToSimplex, sx.spineToSimplex
-/
def spineToDiagonal : Path X m -> X _⦋1⦌ₙ₊₁ :=
  X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

end autoParam

/--
lemma `isStrictSegal` / 引理 `isStrictSegal`

English:
lemma isStrictSegal
  given: (sx : StrictSegal X)
  statement: IsStrictSegal X where
  proof: sx.spineEquiv m h

中文:
引理 isStrictSegal
  条件: (sx : StrictSegal X)
  结论: IsStrictSegal X where
  证明: sx.spineEquiv m h

Depends on / 依赖: spineEquiv, sx.spineEquiv
-/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
.bijective spine_bijective m h := sx.spineEquiv m h

variable (m : Nat) (h : m <= n + 1)

@[simp]
/--
theorem `spineToSimplex_vertex` / 定理 `spineToSimplex_vertex`

English:
theorem spineToSimplex_vertex
  given: (i : Fin (m + 1)) (f : Path X m)
  proof: by
  rw [← spine_vertex]; rw [spine_spineToSimplex_apply]

@[simp]

中文:
定理 spineToSimplex_vertex
  条件: (i : Fin (m + 1)) (f : Path X m)
  证明: by
  rw [← spine_vertex]; rw [spine_spineToSimplex_apply]

@[simp]

Depends on / 依赖: spine_spineToSimplex_apply, spine_vertex
-/
theorem spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) :
    X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op (sx.spineToSimplex m h f) =
      f.vertex i := by
  rw [← spine_vertex]; rw [spine_spineToSimplex_apply]

@[simp]
/--
theorem `spineToSimplex_arrow` / 定理 `spineToSimplex_arrow`

English:
theorem spineToSimplex_arrow
  given: (i : Fin m) (f : Path X m)
  proof: by
  rw [← spine_arrow]; rw [spine_spineToSimplex_apply]

中文:
定理 spineToSimplex_arrow
  条件: (i : Fin m) (f : Path X m)
  证明: by
  rw [← spine_arrow]; rw [spine_spineToSimplex_apply]

Depends on / 依赖: spine_arrow, spine_spineToSimplex_apply
-/
theorem spineToSimplex_arrow (i : Fin m) (f : Path X m) :
    X.map (tr (mkOfSucc i)).op (sx.spineToSimplex m h f) = f.arrow i := by
  rw [← spine_arrow]; rw [spine_spineToSimplex_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `spineToSimplex_interval` / 定理 `spineToSimplex_interval`

English:
theorem spineToSimplex_interval
  given: (f : Path X m) (j l : Nat) (hjl : j + l <= m)
  proof: by
  apply sx.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]
convert! spine_map_subinterval X m h j l hjl sx.spineToSimplex m h f
.symm exact sx.spine_spineToSimplex_apply m h f

中文:
定理 spineToSimplex_interval
  条件: (f : Path X m) (j l : 自然数) (hjl : j + l <= m)
  证明: by
  apply sx.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]
convert! spine_map_subinterval X m h j l hjl sx.spineToSimplex m h f
.symm exact sx.spine_spineToSimplex_apply m h f

Depends on / 依赖: Equiv.coe_fn_mk, coe_fn_mk, convert, spineEquiv, spineInjective, spineToSimplex, spine_map_subinterval, spine_spineToSimplex_apply, sx.spineInjective, sx.spineToSimplex, sx.spine_spineToSimplex_apply
-/
theorem spineToSimplex_interval (f : Path X m) (j l : Nat) (hjl : j + l <= m) :
    X.map (tr (subinterval j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToSimplex l _ (f.interval j l hjl) := by
  apply sx.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]
convert! spine_map_subinterval X m h j l hjl sx.spineToSimplex m h f
.symm exact sx.spine_spineToSimplex_apply m h f

/--
theorem `spineToSimplex_edge` / 定理 `spineToSimplex_edge`

English:
theorem spineToSimplex_edge
  given: (f : Path X m) (j l : Nat) (hjl : j + l <= m)
  proof: by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [diag_subinterval_eq]

中文:
定理 spineToSimplex_edge
  条件: (f : Path X m) (j l : 自然数) (hjl : j + l <= m)
  证明: by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [diag_subinterval_eq]

Depends on / 依赖: Function, Function.comp_apply, Functor, Functor.map_comp_apply, comp_apply, diag_subinterval_eq, map_comp_apply, op_comp, spineToDiagonal, spineToSimplex_interval, tr_comp
-/
theorem spineToSimplex_edge (f : Path X m) (j l : Nat) (hjl : j + l <= m) :
    X.map (tr (intervalEdge j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToDiagonal l (by lia) (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [diag_subinterval_eq]

end spineToSimplex

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `spineToSimplex_map` / 引理 `spineToSimplex_map`

English:
lemma spineToSimplex_map
  statement: {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
  proof: by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _)]; rw [← σ.naturality]
  simp [-NatTrans.naturality]

中文:
引理 spineToSimplex_map
  结论: {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
  证明: by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _)]; rw [← σ.naturality]
  simp [-NatTrans.naturality]

Depends on / 依赖: Equiv.coe_fn_mk, NatTrans, NatTrans.naturality, Y.map, coe_fn_mk, naturality, spineEquiv, spineInjective, spine_arrow, sy.spineInjective, types_comp_apply
-/
lemma spineToSimplex_map {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
    (sy : StrictSegal Y) (m : Nat) (h : m <= n) (f : Path X (m + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (m + 1) _ (f.map σ) =
      σ.app (op ⦋m + 1⦌ₙ₊₁) (sx.spineToSimplex (m + 1) _ f) := by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _)]; rw [← σ.naturality]
  simp [-NatTrans.naturality]

section spine_δ

variable (m : Nat) (h : m <= n) (f : Path X (m + 1))
variable {i : Fin (m + 1)} {j : Fin (m + 2)}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `spine_δ_vertex_lt` / 引理 `spine_δ_vertex_lt`

English:
lemma spine_δ_vertex_lt
  given: (hij : i.castSucc < j)
  proof: by
  rw [spine_vertex]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of

中文:
引理 spine_δ_vertex_lt
  条件: (hij : i.castSucc < j)
  证明: by
  rw [spine_vertex]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of

Depends on / 依赖: Fin.succAboveOrderEmb_apply, Fin.succAbove_of_castSucc_lt, Functor, Functor.map_comp_apply, Hom.toOrderHom_mk, OrderEmbedding, OrderEmbedding.toOrderHom_coe, SimplexCategory, SimplexCategory.const_comp, const_comp, len_mk, map_comp_apply, op_comp, spineToSimplex_vertex, spine_vertex, succAboveOrderEmb_apply, succAbove_of_castSucc_lt, toOrderHom_coe, toOrderHom_mk, tr_comp
-/
lemma spine_δ_vertex_lt (hij : i.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.castSucc := by
  rw [spine_vertex]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_castSucc_lt j i hij]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `spine_δ_vertex_ge` / 引理 `spine_δ_vertex_ge`

English:
lemma spine_δ_vertex_ge
  given: (hij : j <= i.castSucc)
  proof: by
  rw [spine_vertex]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of

中文:
引理 spine_δ_vertex_ge
  条件: (hij : j <= i.castSucc)
  证明: by
  rw [spine_vertex]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of

Depends on / 依赖: Fin.succAboveOrderEmb_apply, Fin.succAbove_of_le_castSucc, Functor, Functor.map_comp_apply, Hom.toOrderHom_mk, OrderEmbedding, OrderEmbedding.toOrderHom_coe, SimplexCategory, SimplexCategory.const_comp, const_comp, len_mk, map_comp_apply, op_comp, spineToSimplex_vertex, spine_vertex, succAboveOrderEmb_apply, succAbove_of_le_castSucc, toOrderHom_coe, toOrderHom_mk, tr_comp
-/
lemma spine_δ_vertex_ge (hij : j <= i.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.succ := by
  rw [spine_vertex]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_le_castSucc j i hij]

variable {i : Fin m} {j : Fin (m + 2)}

/--
lemma `spine_δ_arrow_lt` / 引理 `spine_δ_arrow_lt`

English:
lemma spine_δ_arrow_lt
  given: (hij : i.succ.castSucc < j)
  proof: by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_lt hij]; rw [spineToSimplex_arrow]

中文:
引理 spine_δ_arrow_lt
  条件: (hij : i.succ.castSucc < j)
  证明: by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_lt hij]; rw [spineToSimplex_arrow]

Depends on / 依赖: Functor, Functor.map_comp_apply, map_comp_apply, op_comp, spineToSimplex_arrow, spine_arrow, tr_comp
-/
lemma spine_δ_arrow_lt (hij : i.succ.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.castSucc := by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_lt hij]; rw [spineToSimplex_arrow]

/--
lemma `spine_δ_arrow_gt` / 引理 `spine_δ_arrow_gt`

English:
lemma spine_δ_arrow_gt
  given: (hij : j < i.succ.castSucc)
  proof: by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_gt hij]; rw [spineToSimplex_arrow]

中文:
引理 spine_δ_arrow_gt
  条件: (hij : j < i.succ.castSucc)
  证明: by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_gt hij]; rw [spineToSimplex_arrow]

Depends on / 依赖: Functor, Functor.map_comp_apply, map_comp_apply, op_comp, spineToSimplex_arrow, spine_arrow, tr_comp
-/
lemma spine_δ_arrow_gt (hij : j < i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.succ := by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_gt hij]; rw [spineToSimplex_arrow]

end spine_δ

variable {X : SSet.Truncated.{u} (n + 2)} (sx : StrictSegal X) (m : Nat)
  (h : m <= n + 1) (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}

/--
lemma `spine_δ_arrow_eq` / 引理 `spine_δ_arrow_eq`

English:
lemma spine_δ_arrow_eq
  given: (hij : j = i.succ.castSucc)
  proof: by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_eq hij]; rw [spineToSimplex_edge]

中文:
引理 spine_δ_arrow_eq
  条件: (hij : j = i.succ.castSucc)
  证明: by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_eq hij]; rw [spineToSimplex_edge]

Depends on / 依赖: Functor, Functor.map_comp_apply, map_comp_apply, op_comp, spineToSimplex_edge, spine_arrow, tr_comp
-/
lemma spine_δ_arrow_eq (hij : j = i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i =
      sx.spineToDiagonal 2 (by lia) (f.interval i 2 (by lia)) := by
  rw [spine_arrow]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [← tr_comp]; rw [mkOfSucc_δ_eq hij]; rw [spineToSimplex_edge]

end StrictSegal
end Truncated

variable (X : SSet.{u})

/--
Definition of `StrictSegal` / `StrictSegal` 的定义

English:
structure StrictSegal
  parameters: where
  axioms and operations (3):
    - spineToSimplex({n : Nat}) : Path X n -> X _⦋n⦌
    - spine_spineToSimplex((n : Nat)) : spine X n ∘ spineToSimplex = id
    - spineToSimplex_spine((n : Nat)) : spineToSimplex ∘ spine X n = id

中文:
结构 StrictSegal
  参数: where
  公理与运算 (3 个):
    - spineToSimplex({n : 自然数}) : Path X n -> X _⦋n⦌
    - spine_spineToSimplex((n : 自然数)) : spine X n ∘ spineToSimplex = id
    - spineToSimplex_spine((n : 自然数)) : spineToSimplex ∘ spine X n = id
-/
structure StrictSegal where
  /-- The inverse to `spine X n`. -/
  spineToSimplex {n : Nat} : Path X n -> X _⦋n⦌
  /-- `spineToSimplex` is a right inverse to `spine X n`. -/
  spine_spineToSimplex (n : Nat) : spine X n ∘ spineToSimplex = id
  /-- `spineToSimplex` is a left inverse to `spine X n`. -/
  spineToSimplex_spine (n : Nat) : spineToSimplex ∘ spine X n = id

/--
Definition of `IsStrictSegal` / `IsStrictSegal` 的定义

English:
class IsStrictSegal
  parameters: : Prop where
  axioms and operations (1):
    - segal((n : Nat)) : Function.Bijective (spine X n)

中文:
类 IsStrictSegal
  参数: : 命题 where
  公理与运算 (1 个):
    - segal((n : 自然数)) : Function.Bijective (spine X n)
-/
class IsStrictSegal : Prop where
  segal (n : Nat) : Function.Bijective (spine X n)

namespace StrictSegal

/--
Definition of `ofIsStrictSegal` / `ofIsStrictSegal` 的定义

English:
definition ofIsStrictSegal
  signature: [IsStrictSegal X]
  body: .invFun Equiv.ofBijective (X.spine n) (IsStrictSegal.segal n)
  spine_spineToSimplex n :=
funext .right_inv Equiv.ofBijective (X.spine n) _
  spineToSimplex_spine n :=
funext .left_inv Equiv.ofBijective (X.spine n) _

中文:
定义 ofIsStrictSegal
  签名: [IsStrictSegal X]
  定义体: .invFun Equiv.ofBijective (X.spine n) (IsStrictSegal.segal n)
  spine_spineToSimplex n :=
funext .right_inv Equiv.ofBijective (X.spine n) _
  spineToSimplex_spine n :=
funext .left_inv Equiv.ofBijective (X.spine n) _

Depends on / 依赖: Equiv.ofBijective, IsStrictSegal, IsStrictSegal.segal, X.spine, invFun, left_inv, ofBijective, right_inv, spineToSimplex_spine, spine_spineToSimplex
-/
noncomputable def ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where
  spineToSimplex {n} :=
.invFun Equiv.ofBijective (X.spine n) (IsStrictSegal.segal n)
  spine_spineToSimplex n :=
funext .right_inv Equiv.ofBijective (X.spine n) _
  spineToSimplex_spine n :=
funext .left_inv Equiv.ofBijective (X.spine n) _

variable {X} (sx : StrictSegal X)

/-- A `StrictSegal` structure on a simplicial set `X` restricts to a
`Truncated.StrictSegal` structure on the `n + 1`-truncation of `X`. -/
.StrictSegal where .obj X protected def truncation (n : Nat) : truncation (n + 1)
  spineToSimplex _ _ := sx.spineToSimplex
  spine_spineToSimplex m _ := sx.spine_spineToSimplex m
  spineToSimplex_spine m _ := sx.spineToSimplex_spine m

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.IsStrictSegal]
  signature: (n : Nat)
  body: ((ofIsStrictSegal X).truncation n).isStrictSegal

@[simp]

中文:
实例 [X.IsStrictSegal]
  签名: (n : 自然数)
  定义体: ((ofIsStrictSegal X).truncation n).isStrictSegal

@[simp]

Depends on / 依赖: isStrictSegal, ofIsStrictSegal, truncation
-/
instance [X.IsStrictSegal] (n : Nat) :
    ((truncation (n + 1)).obj X).IsStrictSegal :=
  ((ofIsStrictSegal X).truncation n).isStrictSegal

@[simp]
/--
lemma `spine_spineToSimplex_apply` / 引理 `spine_spineToSimplex_apply`

English:
lemma spine_spineToSimplex_apply
  given: {n : Nat} (f : Path X n)
  proof: congr_fun (sx.spine_spineToSimplex n) f

@[simp]

中文:
引理 spine_spineToSimplex_apply
  条件: {n : 自然数} (f : Path X n)
  证明: congr_fun (sx.spine_spineToSimplex n) f

@[simp]

Depends on / 依赖: congr_fun, spine_spineToSimplex, sx.spine_spineToSimplex
-/
lemma spine_spineToSimplex_apply {n : Nat} (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f :=
  congr_fun (sx.spine_spineToSimplex n) f

@[simp]
/--
lemma `spineToSimplex_spine_apply` / 引理 `spineToSimplex_spine_apply`

English:
lemma spineToSimplex_spine_apply
  given: {n : Nat} (Δ : X _⦋n⦌)
  proof: congr_fun (sx.spineToSimplex_spine n) Δ

中文:
引理 spineToSimplex_spine_apply
  条件: {n : 自然数} (Δ : X _⦋n⦌)
  证明: congr_fun (sx.spineToSimplex_spine n) Δ

Depends on / 依赖: congr_fun, spineToSimplex_spine, sx.spineToSimplex_spine
-/
lemma spineToSimplex_spine_apply {n : Nat} (Δ : X _⦋n⦌) :
    sx.spineToSimplex (X.spine n Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine n) Δ

/--
Definition of `spineEquiv` / `spineEquiv` 的定义

English:
definition spineEquiv
  signature: (n : Nat)
  body: X.spine n
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

中文:
定义 spineEquiv
  签名: (n : 自然数)
  定义体: X.spine n
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

Depends on / 依赖: X.spine
-/
def spineEquiv (n : Nat) : X _⦋n⦌ ≃ Path X n where
  toFun := X.spine n
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

variable {n : Nat}

/--
theorem `spineInjective` / 定理 `spineInjective`

English:
theorem spineInjective
  statement: Function.Injective (sx.spineEquiv n)
  proof: Equiv.injective _

中文:
定理 spineInjective
  结论: Function.Injective (sx.spineEquiv n)
  证明: Equiv.injective _

Depends on / 依赖: Equiv.injective, injective
-/
theorem spineInjective : Function.Injective (sx.spineEquiv n) :=
  Equiv.injective _

/--
lemma `isStrictSegal` / 引理 `isStrictSegal`

English:
lemma isStrictSegal
  given: (sx : StrictSegal X)
  statement: IsStrictSegal X where
  proof: sx.spineEquiv n

@[simp]

中文:
引理 isStrictSegal
  条件: (sx : StrictSegal X)
  结论: IsStrictSegal X where
  证明: sx.spineEquiv n

@[simp]

Depends on / 依赖: spineEquiv, sx.spineEquiv
-/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
.bijective segal n := sx.spineEquiv n

@[simp]
/--
theorem `spineToSimplex_vertex` / 定理 `spineToSimplex_vertex`

English:
theorem spineToSimplex_vertex
  given: (i : Fin (n + 1)) (f : Path X n)
  proof: by
  rw [← spine_vertex]; rw [spine_spineToSimplex_apply]

@[simp]

中文:
定理 spineToSimplex_vertex
  条件: (i : Fin (n + 1)) (f : Path X n)
  证明: by
  rw [← spine_vertex]; rw [spine_spineToSimplex_apply]

@[simp]

Depends on / 依赖: spine_spineToSimplex_apply, spine_vertex
-/
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (sx.spineToSimplex f) =
      f.vertex i := by
  rw [← spine_vertex]; rw [spine_spineToSimplex_apply]

@[simp]
/--
theorem `spineToSimplex_arrow` / 定理 `spineToSimplex_arrow`

English:
theorem spineToSimplex_arrow
  given: (i : Fin n) (f : Path X n)
  proof: by
  rw [← spine_arrow]; rw [spine_spineToSimplex_apply]

中文:
定理 spineToSimplex_arrow
  条件: (i : Fin n) (f : Path X n)
  证明: by
  rw [← spine_arrow]; rw [spine_spineToSimplex_apply]

Depends on / 依赖: spine_arrow, spine_spineToSimplex_apply
-/
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow]; rw [spine_spineToSimplex_apply]

/--
Definition of `spineToDiagonal` / `spineToDiagonal` 的定义

English:
definition spineToDiagonal
  signature: (f : Path X n)
  body: SimplicialObject.diagonal X (sx.spineToSimplex f)

中文:
定义 spineToDiagonal
  签名: (f : Path X n)
  定义体: SimplicialObject.diagonal X (sx.spineToSimplex f)

Depends on / 依赖: SimplicialObject, SimplicialObject.diagonal, diagonal, spineToSimplex, sx.spineToSimplex
-/
def spineToDiagonal (f : Path X n) : X _⦋1⦌ :=
  SimplicialObject.diagonal X (sx.spineToSimplex f)

section interval

variable (f : Path X n) (j l : Nat) (hjl : j + l <= n)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `spineToSimplex_interval` / 定理 `spineToSimplex_interval`

English:
theorem spineToSimplex_interval
  proof: by
  apply sx.spineInjective
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]; rw [spine_map_subinterval]; rw [spine_spineToSimplex_apply]

中文:
定理 spineToSimplex_interval
  证明: by
  apply sx.spineInjective
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]; rw [spine_map_subinterval]; rw [spine_spineToSimplex_apply]

Depends on / 依赖: Equiv.coe_fn_mk, coe_fn_mk, spineEquiv, spineInjective, spine_map_subinterval, spine_spineToSimplex_apply, sx.spineInjective
-/
theorem spineToSimplex_interval :
    X.map (subinterval j l hjl).op (sx.spineToSimplex f) =
      sx.spineToSimplex (f.interval j l hjl) := by
  apply sx.spineInjective
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]; rw [spine_map_subinterval]; rw [spine_spineToSimplex_apply]

/--
theorem `spineToSimplex_edge` / 定理 `spineToSimplex_edge`

English:
theorem spineToSimplex_edge
  proof: by
  dsimp only [spineToDiagonal, SimplicialObject.diagonal]
  rw [← spineToSimplex_interval]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [diag_subinterval_eq]

中文:
定理 spineToSimplex_edge
  证明: by
  dsimp only [spineToDiagonal, SimplicialObject.diagonal]
  rw [← spineToSimplex_interval]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [diag_subinterval_eq]

Depends on / 依赖: Functor, Functor.map_comp_apply, SimplicialObject, SimplicialObject.diagonal, diag_subinterval_eq, diagonal, map_comp_apply, op_comp, spineToDiagonal, spineToSimplex_interval
-/
theorem spineToSimplex_edge :
    X.map (intervalEdge j l hjl).op (sx.spineToSimplex f) =
      sx.spineToDiagonal (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, SimplicialObject.diagonal]
  rw [← spineToSimplex_interval]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [diag_subinterval_eq]

end interval

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `spineToSimplex_map` / 引理 `spineToSimplex_map`

English:
lemma spineToSimplex_map
  statement: {X Y : SSet.{u}} (sx : StrictSegal X)
  proof: by
  apply sy.spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _)]; rw [← σ.naturality]; rw [types_comp_apply]; rw [spineToSimplex_arrow]; rw [spineToSimplex_arrow]; rw [Path.map_arrow]

中文:
引理 spineToSimplex_map
  结论: {X Y : SSet.{u}} (sx : StrictSegal X)
  证明: by
  apply sy.spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _)]; rw [← σ.naturality]; rw [types_comp_apply]; rw [spineToSimplex_arrow]; rw [spineToSimplex_arrow]; rw [Path.map_arrow]

Depends on / 依赖: Equiv.coe_fn_mk, Path.map_arrow, Y.map, coe_fn_mk, map_arrow, naturality, spineEquiv, spineInjective, spineToSimplex_arrow, spine_arrow, sy.spineInjective, types_comp_apply
-/
lemma spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X)
    (sy : StrictSegal Y) {n : Nat} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (f.map σ) = σ.app _ (sx.spineToSimplex f) := by
  apply sy.spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _)]; rw [← σ.naturality]; rw [types_comp_apply]; rw [spineToSimplex_arrow]; rw [spineToSimplex_arrow]; rw [Path.map_arrow]

variable (f : Path X (n + 1))
variable {i : Fin (n + 1)} {j : Fin (n + 2)}

/--
lemma `spine_δ_vertex_lt` / 引理 `spine_δ_vertex_lt`

English:
lemma spine_δ_vertex_lt
  given: (h : i.castSucc < j)
  proof: by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [

中文:
引理 spine_δ_vertex_lt
  条件: (h : i.castSucc < j)
  证明: by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [

Depends on / 依赖: Fin.succAboveOrderEmb_apply, Fin.succAbove_of_castSucc_lt, Functor, Functor.map_comp_apply, Hom.mk, Hom.toOrderHom, OrderEmbedding, OrderEmbedding.toOrderHom_coe, SimplexCategory, SimplexCategory.const_comp, SimplicialObject, const_comp, len_mk, map_comp_apply, op_comp, spineToSimplex_vertex, spine_vertex, succAboveOrderEmb_apply, succAbove_of_castSucc_lt, toOrderHom
-/
lemma spine_δ_vertex_lt (h : i.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i =
      f.vertex i.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i h]

/--
lemma `spine_δ_vertex_ge` / 引理 `spine_δ_vertex_ge`

English:
lemma spine_δ_vertex_ge
  given: (h : j <= i.castSucc)
  proof: by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [

中文:
引理 spine_δ_vertex_ge
  条件: (h : j <= i.castSucc)
  证明: by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [

Depends on / 依赖: Fin.succAboveOrderEmb_apply, Fin.succAbove_of_le_castSucc, Functor, Functor.map_comp_apply, Hom.mk, Hom.toOrderHom, OrderEmbedding, OrderEmbedding.toOrderHom_coe, SimplexCategory, SimplexCategory.const_comp, SimplicialObject, const_comp, len_mk, map_comp_apply, op_comp, spineToSimplex_vertex, spine_vertex, succAboveOrderEmb_apply, succAbove_of_le_castSucc, toOrderHom
-/
lemma spine_δ_vertex_ge (h : j <= i.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [SimplexCategory.const_comp]; rw [spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc j i h]

variable {i : Fin n} {j : Fin (n + 2)}

/--
lemma `spine_δ_arrow_lt` / 引理 `spine_δ_arrow_lt`

English:
lemma spine_δ_arrow_lt
  given: (h : i.succ.castSucc < j)
  proof: by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_lt h]; rw [spineToSimplex_arrow]

中文:
引理 spine_δ_arrow_lt
  条件: (h : i.succ.castSucc < j)
  证明: by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_lt h]; rw [spineToSimplex_arrow]

Depends on / 依赖: Functor, Functor.map_comp_apply, SimplicialObject, map_comp_apply, op_comp, spineToSimplex_arrow, spine_arrow
-/
lemma spine_δ_arrow_lt (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_lt h]; rw [spineToSimplex_arrow]

/--
lemma `spine_δ_arrow_gt` / 引理 `spine_δ_arrow_gt`

English:
lemma spine_δ_arrow_gt
  given: (h : j < i.succ.castSucc)
  proof: by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_gt h]; rw [spineToSimplex_arrow]

中文:
引理 spine_δ_arrow_gt
  条件: (h : j < i.succ.castSucc)
  证明: by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_gt h]; rw [spineToSimplex_arrow]

Depends on / 依赖: Functor, Functor.map_comp_apply, SimplicialObject, map_comp_apply, op_comp, spineToSimplex_arrow, spine_arrow
-/
lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_gt h]; rw [spineToSimplex_arrow]

/--
lemma `spine_δ_arrow_eq` / 引理 `spine_δ_arrow_eq`

English:
lemma spine_δ_arrow_eq
  given: (h : j = i.succ.castSucc)
  proof: by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_eq h]; rw [spineToSimplex_edge]

中文:
引理 spine_δ_arrow_eq
  条件: (h : j = i.succ.castSucc)
  证明: by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_eq h]; rw [spineToSimplex_edge]

Depends on / 依赖: Functor, Functor.map_comp_apply, SimplicialObject, map_comp_apply, op_comp, spineToSimplex_edge, spine_arrow
-/
lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i =
      sx.spineToDiagonal (f.interval i 2 (by lia)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply]; rw [← op_comp]
  rw [mkOfSucc_δ_eq h]; rw [spineToSimplex_edge]

end StrictSegal

/--
Definition of `StrictSegalCore` / `StrictSegalCore` 的定义

English:
structure StrictSegalCore
  parameters: (n : Nat)
  axioms and operations (4):
    - concat((x : X _⦋1⦌) (s : X _⦋n⦌) (h : X.δ 0 x = X.map (SimplexCategory.const _ _ 0).op s)) : X _⦋n + 1⦌
    - map_mkOfSucc_zero_concat(x s h) : X.map (mkOfSucc 0).op (concat x s h) = x
    - δ₀_concat(x s h) : X.δ 0 (concat x s h) = s
    - injective({x y : X _⦋n + 1⦌} (h : X.map (mkOfSucc 0).op x = X.map (mkOfSucc 0).op y) (h₀ : X.δ 0 x = X.δ 0 y)) : x = y

中文:
结构 StrictSegalCore
  参数: (n : 自然数)
  公理与运算 (4 个):
    - concat((x : X _⦋1⦌) (s : X _⦋n⦌) (h : X.δ 0 x = X.map (SimplexCategory.const _ _ 0).op s)) : X _⦋n + 1⦌
    - map_mkOfSucc_zero_concat(x s h) : X.map (mkOfSucc 0).op (concat x s h) = x
    - δ₀_concat(x s h) : X.δ 0 (concat x s h) = s
    - injective({x y : X _⦋n + 1⦌} (h : X.map (mkOfSucc 0).op x = X.map (mkOfSucc 0).op y) (h₀ : X.δ 0 x = X.δ 0 y)) : x = y
-/
structure StrictSegalCore (n : Nat) where
  /-- Map which produces an `n + 1`-simplex from a `1`-simplex and an `n`-simplex when
  the target vertex of the `1`-simplex equals the zeroth simplex of the `n`-simplex. -/
  concat (x : X _⦋1⦌) (s : X _⦋n⦌) (h : X.δ 0 x = X.map (SimplexCategory.const _ _ 0).op s) :
    X _⦋n + 1⦌
  map_mkOfSucc_zero_concat x s h : X.map (mkOfSucc 0).op (concat x s h) = x
  δ₀_concat x s h : X.δ 0 (concat x s h) = s
  injective {x y : X _⦋n + 1⦌} (h : X.map (mkOfSucc 0).op x = X.map (mkOfSucc 0).op y)
    (h₀ : X.δ 0 x = X.δ 0 y) : x = y

namespace StrictSegalCore

variable {X} (h : forall n, X.StrictSegalCore n) {n : Nat} (p : X.Path n)

/--
Definition of `spineToSimplexAux` / `spineToSimplexAux` 的定义

English:
definition spineToSimplexAux
  signature: : { s : X _⦋n⦌ // X.spine _ s = p }
  body: by
  induction n with
  | zero => exact ⟨p.vertex 0, by aesop⟩
  | succ n hn =>
    refine ⟨(h n).concat (p.arrow 0) (hn (p.interval 1 n)).val ?_, ?_⟩
    · rw [p.arrow_tgt 0]
      exact Path.congr_vertex (hn (p.interval 1 n)).prop.symm 0
    · ext i
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_s

中文:
定义 spineToSimplexAux
  签名: : { s : X _⦋n⦌ // X.spine _ s = p }
  定义体: by
  induction n with
  | zero => exact ⟨p.vertex 0, by aesop⟩
  | succ n hn =>
    refine ⟨(h n).concat (p.arrow 0) (hn (p.interval 1 n)).val ?_, ?_⟩
    · rw [p.arrow_tgt 0]
      exact Path.congr_vertex (hn (p.interval 1 n)).prop.symm 0
    · ext i
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_s

Depends on / 依赖: Functor, Functor.map_comp_apply, Path.congr_vertex, SimplexCategory, SimplexCategory.mkOfSucc_, SimplicialObject, arrow_interval, arrow_tgt, concat, congr_vertex, eq_zero_or_eq_succ, i.eq_zero_or_eq_succ, i.succ, interval, map_comp_apply, map_mkOfSucc_zero_concat, op_comp, p.arrow, p.arrow_interval, p.arrow_tgt
-/
def spineToSimplexAux : { s : X _⦋n⦌ // X.spine _ s = p } := by
  induction n with
  | zero => exact ⟨p.vertex 0, by aesop⟩
  | succ n hn =>
    refine ⟨(h n).concat (p.arrow 0) (hn (p.interval 1 n)).val ?_, ?_⟩
    · rw [p.arrow_tgt 0]
      exact Path.congr_vertex (hn (p.interval 1 n)).prop.symm 0
    · ext i
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · dsimp
        rw [map_mkOfSucc_zero_concat]
      · simpa [spine_arrow, ← SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp),
          op_comp, Functor.map_comp_apply, ← SimplicialObject.δ_def, δ₀_concat,
          ← p.arrow_interval 1 n i i.succ (by grind) (by grind)] using
            Path.congr_arrow (hn (p.interval 1 n)).prop i

/--
Definition of `spineToSimplex` / `spineToSimplex` 的定义

English:
definition spineToSimplex
  signature: : X _⦋n⦌
  body: (spineToSimplexAux h p).val

@[simp]

中文:
定义 spineToSimplex
  签名: : X _⦋n⦌
  定义体: (spineToSimplexAux h p).val

@[simp]

Depends on / 依赖: spineToSimplexAux
-/
def spineToSimplex : X _⦋n⦌ := (spineToSimplexAux h p).val

@[simp]
/--
lemma `spine_spineToSimplex` / 引理 `spine_spineToSimplex`

English:
lemma spine_spineToSimplex
  statement: X.spine n (spineToSimplex h p) = p
  proof: (spineToSimplexAux h p).prop

中文:
引理 spine_spineToSimplex
  结论: X.spine n (spineToSimplex h p) = p
  证明: (spineToSimplexAux h p).prop

Depends on / 依赖: spineToSimplexAux
-/
lemma spine_spineToSimplex : X.spine n (spineToSimplex h p) = p := (spineToSimplexAux h p).prop

/--
lemma `spineToSimplex_zero` / 引理 `spineToSimplex_zero`

English:
lemma spineToSimplex_zero
  given: (p : X.Path 0)
  statement: spineToSimplex h p = p.vertex 0
  proof: rfl

中文:
引理 spineToSimplex_zero
  条件: (p : X.Path 0)
  结论: spineToSimplex h p = p.vertex 0
  证明: rfl
-/
lemma spineToSimplex_zero (p : X.Path 0) : spineToSimplex h p = p.vertex 0 := rfl

/--
lemma `spineToSimplex_succ` / 引理 `spineToSimplex_succ`

English:
lemma spineToSimplex_succ
  given: (p : X.Path (n + 1))
  proof: rfl

中文:
引理 spineToSimplex_succ
  条件: (p : X.Path (n + 1))
  证明: rfl
-/
lemma spineToSimplex_succ (p : X.Path (n + 1)) :
    spineToSimplex h p = (h n).concat (p.arrow 0) (spineToSimplex h (p.interval 1 n)) (by
      rw [p.arrow_tgt 0]
      exact Path.congr_vertex (spine_spineToSimplex h (p.interval 1 n)).symm 0) :=
  rfl

/--
lemma `map_mkOfSucc_zero_spineToSimplex` / 引理 `map_mkOfSucc_zero_spineToSimplex`

English:
lemma map_mkOfSucc_zero_spineToSimplex
  given: (p : X.Path (n + 1))
  proof: by
  rw [spineToSimplex_succ]; rw [map_mkOfSucc_zero_concat]

中文:
引理 map_mkOfSucc_zero_spineToSimplex
  条件: (p : X.Path (n + 1))
  证明: by
  rw [spineToSimplex_succ]; rw [map_mkOfSucc_zero_concat]

Depends on / 依赖: map_mkOfSucc_zero_concat, spineToSimplex_succ
-/
lemma map_mkOfSucc_zero_spineToSimplex (p : X.Path (n + 1)) :
    X.map (mkOfSucc 0).op (spineToSimplex h p) = p.arrow 0 := by
  rw [spineToSimplex_succ]; rw [map_mkOfSucc_zero_concat]

/--
lemma `δ₀_spineToSimplex` / 引理 `δ₀_spineToSimplex`

English:
lemma δ₀_spineToSimplex
  given: (p : X.Path (n + 1))
  proof: by
  rw [spineToSimplex_succ]; rw [δ₀_concat]

@[simp]

中文:
引理 δ₀_spineToSimplex
  条件: (p : X.Path (n + 1))
  证明: by
  rw [spineToSimplex_succ]; rw [δ₀_concat]

@[simp]

Depends on / 依赖: spineToSimplex_succ
-/
lemma δ₀_spineToSimplex (p : X.Path (n + 1)) :
    X.δ 0 (spineToSimplex h p) = spineToSimplex h (p.interval 1 n) := by
  rw [spineToSimplex_succ]; rw [δ₀_concat]

@[simp]
/--
lemma `spineToSimplex_spine` / 引理 `spineToSimplex_spine`

English:
lemma spineToSimplex_spine
  given: (s : X _⦋n⦌)
  statement: spineToSimplex h (X.spine _ s) = s
  proof: by
  induction n with
  | zero => simp [spineToSimplex_zero]
  | succ n hn =>
    exact (h n).injective (map_mkOfSucc_zero_spineToSimplex _ _)
      (by rw [δ₀_spineToSimplex, ← hn (X.δ 0 s), spine_δ₀])

中文:
引理 spineToSimplex_spine
  条件: (s : X _⦋n⦌)
  结论: spineToSimplex h (X.spine _ s) = s
  证明: by
  induction n with
  | zero => simp [spineToSimplex_zero]
  | succ n hn =>
    exact (h n).injective (map_mkOfSucc_zero_spineToSimplex _ _)
      (by rw [δ₀_spineToSimplex, ← hn (X.δ 0 s), spine_δ₀])

Depends on / 依赖: injective, map_mkOfSucc_zero_spineToSimplex, spineToSimplex_zero
-/
lemma spineToSimplex_spine (s : X _⦋n⦌) : spineToSimplex h (X.spine _ s) = s := by
  induction n with
  | zero => simp [spineToSimplex_zero]
  | succ n hn =>
    exact (h n).injective (map_mkOfSucc_zero_spineToSimplex _ _)
      (by rw [δ₀_spineToSimplex, ← hn (X.δ 0 s), spine_δ₀])

end StrictSegalCore

variable {X} in
/--
Definition of `StrictSegal.ofCore` / `StrictSegal.ofCore` 的定义

English:
definition StrictSegal.ofCore
  signature: (h : forall n, X.StrictSegalCore n)
  body: StrictSegalCore.spineToSimplex h
  spine_spineToSimplex := by aesop
  spineToSimplex_spine n := by aesop

中文:
定义 StrictSegal.ofCore
  签名: (h : 对任意 n, X.StrictSegalCore n)
  定义体: StrictSegalCore.spineToSimplex h
  spine_spineToSimplex := by aesop
  spineToSimplex_spine n := by aesop

Depends on / 依赖: StrictSegalCore, StrictSegalCore.spineToSimplex, spineToSimplex
-/
def StrictSegal.ofCore (h : forall n, X.StrictSegalCore n) : X.StrictSegal where
  spineToSimplex := StrictSegalCore.spineToSimplex h
  spine_spineToSimplex := by aesop
  spineToSimplex_spine n := by aesop

end SSet

namespace CategoryTheory.Nerve

open SSet

variable (C : Type u) [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `strictSegal` / `strictSegal` 的定义

English:
definition strictSegal
  signature: : StrictSegal (nerve C)
  body: StrictSegal.ofCore (fun n =>
    { concat f s h := s.precomp (f.hom ≫ eqToHom (Functor.congr_obj h 0))
      map_mkOfSucc_zero_concat f s h :=
        ComposableArrows.ext₁ rfl (Functor.congr_obj h 0).symm (by cat_disch)
      δ₀_concat f s h := rfl
      injective {f g} h h₀ :=
        ComposableAr

中文:
定义 strictSegal
  签名: : StrictSegal (nerve C)
  定义体: StrictSegal.ofCore (fun n =>
    { concat f s h := s.precomp (f.hom ≫ eqToHom (Functor.congr_obj h 0))
      map_mkOfSucc_zero_concat f s h :=
        ComposableArrows.ext₁ rfl (Functor.congr_obj h 0).symm (by cat_disch)
      δ₀_concat f s h := rfl
      injective {f g} h h₀ :=
        ComposableAr

Depends on / 依赖: Arrow.mk_eq_mk_iff, ComposableArrows, ComposableArrows.arrowEquiv, ComposableArrows.ext, ComposableArrows.ext_succ, DFunLike, DFunLike.congr_arg, Functor, Functor.congr_obj, StrictSegal, StrictSegal.ofCore, arrowEquiv, cat_disch, concat, congr_arg, congr_obj, eqToHom, ext_succ, f.hom, injective
-/
def strictSegal : StrictSegal (nerve C) :=
  StrictSegal.ofCore (fun n =>
    { concat f s h := s.precomp (f.hom ≫ eqToHom (Functor.congr_obj h 0))
      map_mkOfSucc_zero_concat f s h :=
        ComposableArrows.ext₁ rfl (Functor.congr_obj h 0).symm (by cat_disch)
      δ₀_concat f s h := rfl
      injective {f g} h h₀ :=
        ComposableArrows.ext_succ (Functor.congr_obj h 0) h₀
          ((Arrow.mk_eq_mk_iff _ _).1
            (DFunLike.congr_arg ComposableArrows.arrowEquiv h)).2.2 })

/--
Instance `isStrictSegal` / 实例 `isStrictSegal`

English:
instance isStrictSegal
  signature: : IsStrictSegal (nerve C)
  body: .isStrictSegal strictSegal C

中文:
实例 isStrictSegal
  签名: : IsStrictSegal (nerve C)
  定义体: .isStrictSegal strictSegal C

Depends on / 依赖: isStrictSegal, strictSegal
-/
instance isStrictSegal : IsStrictSegal (nerve C) :=
.isStrictSegal strictSegal C

end CategoryTheory.Nerve
