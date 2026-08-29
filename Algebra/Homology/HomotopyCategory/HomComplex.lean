/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # The cochain complex of homomorphisms between cochain complexes

If `F` and `G` are cochain complexes (indexed by `ℤ`) in a preadditive category,
there is a cochain complex of abelian groups whose `0`-cocycles identify to
morphisms `F ⟶ G`. Informally, in degree `n`, this complex shall consist of
cochains of degree `n` from `F` to `G`, i.e. arbitrary families for morphisms
`F.X p ⟶ G.X (p + n)`. This complex shall be denoted `HomComplex F G`.

In order to avoid type-theoretic issues, a cochain of degree `n : ℤ`
(i.e. a term of type of `Cochain F G n`) shall be defined here
as the data of a morphism `F.X p ⟶ G.X q` for all triplets
`⟨p, q, hpq⟩` where `p` and `q` are integers and `hpq : p + n = q`.
If `α : Cochain F G n`, we shall define `α.v p q hpq : F.X p ⟶ G.X q`.

We follow the signs conventions appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable {F G K L : CochainComplex C Int} (n m : Int)

namespace HomComplex

/--
Definition of `Triplet` / `Triplet` 的定义

English:
structure Triplet
  parameters: (n : Int)
  axioms and operations (3):
    - p : Int
    - q : Int
    - hpq : p + n = q

中文:
结构 Triplet
  参数: (n : 整数)
  公理与运算 (3 个):
    - p : 整数
    - q : 整数
    - hpq : p + n = q
-/
structure Triplet (n : Int) where
  /-- a first integer -/
  p : Int
  /-- a second integer -/
  q : Int
  /-- the condition on the two integers -/
  hpq : p + n = q

variable (F G)

/--
Definition of `Cochain` / `Cochain` 的定义

English:
definition Cochain
  body: forall (T : Triplet n), F.X T.p ⟶ G.X T.q

中文:
定义 Cochain
  定义体: forall (T : Triplet n), F.X T.p ⟶ G.X T.q

Depends on / 依赖: Triplet
-/
def Cochain := forall (T : Triplet n), F.X T.p ⟶ G.X T.q

namespace Cochain

-- The `SMul` instance exists to avoid a zsmul diamond.
deriving instance SMul R, AddCommGroup, Module R for Cochain F G n

variable {F G n}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q)
  body: fun ⟨p, q, hpq⟩ => v p q hpq

中文:
定义 mk
  签名: (v : 对任意 (p q : 整数) (_ : p + n = q), F.X p ⟶ G.X q)
  定义体: fun ⟨p, q, hpq⟩ => v p q hpq
-/
def mk (v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q) : Cochain F G n :=
  fun ⟨p, q, hpq⟩ => v p q hpq

/--
Definition of `v` / `v` 的定义

English:
definition v
  signature: (γ : Cochain F G n) (p q : Int) (hpq : p + n = q)
  body: γ ⟨p, q, hpq⟩

@[simp]

中文:
定义 v
  签名: (γ : Cochain F G n) (p q : 整数) (hpq : p + n = q)
  定义体: γ ⟨p, q, hpq⟩

@[simp]
-/
def v (γ : Cochain F G n) (p q : Int) (hpq : p + n = q) :
    F.X p ⟶ G.X q := γ ⟨p, q, hpq⟩

@[simp]
/--
lemma `mk_v` / 引理 `mk_v`

English:
lemma mk_v
  given: (v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q) (p q : Int) (hpq : p + n = q)
  proof: rfl

中文:
引理 mk_v
  条件: (v : 对任意 (p q : 整数) (_ : p + n = q), F.X p ⟶ G.X q) (p q : 整数) (hpq : p + n = q)
  证明: rfl
-/
lemma mk_v (v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q) (p q : Int) (hpq : p + n = q) :
    (Cochain.mk v).v p q hpq = v p q hpq := rfl

/--
lemma `congr_v` / 引理 `congr_v`

English:
lemma congr_v
  given: {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q)
  proof: by subst h; rfl

@[ext]

中文:
引理 congr_v
  条件: {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : 整数) (hpq : p + n = q)
  证明: by subst h; rfl

@[ext]
-/
lemma congr_v {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) :
    z₁.v p q hpq = z₂.v p q hpq := by subst h; rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (z₁ z₂ : Cochain F G n)
  proof: by
  funext ⟨p, q, hpq⟩
  apply h

@[ext 1100]

中文:
引理 ext
  结论: (z₁ z₂ : Cochain F G n)
  证明: by
  funext ⟨p, q, hpq⟩
  apply h

@[ext 1100]
-/
lemma ext (z₁ z₂ : Cochain F G n)
    (h : forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂ := by
  funext ⟨p, q, hpq⟩
  apply h

@[ext 1100]
/--
lemma `ext₀` / 引理 `ext₀`

English:
lemma ext₀
  statement: (z₁ z₂ : Cochain F G 0)
  proof: by
  ext
  grind

@[simp]

中文:
引理 ext₀
  结论: (z₁ z₂ : Cochain F G 0)
  证明: by
  ext
  grind

@[simp]
-/
lemma ext₀ (z₁ z₂ : Cochain F G 0)
    (h : forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂ := by
  ext
  grind

@[simp]
/--
lemma `zero_v` / 引理 `zero_v`

English:
lemma zero_v
  given: {n : Int} (p q : Int) (hpq : p + n = q)
  proof: rfl

@[simp]

中文:
引理 zero_v
  条件: {n : 整数} (p q : 整数) (hpq : p + n = q)
  证明: rfl

@[simp]
-/
lemma zero_v {n : Int} (p q : Int) (hpq : p + n = q) :
    (0 : Cochain F G n).v p q hpq = 0 := rfl

@[simp]
/--
lemma `add_v` / 引理 `add_v`

English:
lemma add_v
  given: {n : Int} (z₁ z₂ : Cochain F G n) (p q : Int) (hpq : p + n = q)
  proof: rfl

@[simp]

中文:
引理 add_v
  条件: {n : 整数} (z₁ z₂ : Cochain F G n) (p q : 整数) (hpq : p + n = q)
  证明: rfl

@[simp]
-/
lemma add_v {n : Int} (z₁ z₂ : Cochain F G n) (p q : Int) (hpq : p + n = q) :
    (z₁ + z₂).v p q hpq = z₁.v p q hpq + z₂.v p q hpq := rfl

@[simp]
/--
lemma `sub_v` / 引理 `sub_v`

English:
lemma sub_v
  given: {n : Int} (z₁ z₂ : Cochain F G n) (p q : Int) (hpq : p + n = q)
  proof: rfl

@[simp]

中文:
引理 sub_v
  条件: {n : 整数} (z₁ z₂ : Cochain F G n) (p q : 整数) (hpq : p + n = q)
  证明: rfl

@[simp]
-/
lemma sub_v {n : Int} (z₁ z₂ : Cochain F G n) (p q : Int) (hpq : p + n = q) :
    (z₁ - z₂).v p q hpq = z₁.v p q hpq - z₂.v p q hpq := rfl

@[simp]
/--
lemma `neg_v` / 引理 `neg_v`

English:
lemma neg_v
  given: {n : Int} (z : Cochain F G n) (p q : Int) (hpq : p + n = q)
  proof: rfl

@[simp]

中文:
引理 neg_v
  条件: {n : 整数} (z : Cochain F G n) (p q : 整数) (hpq : p + n = q)
  证明: rfl

@[simp]
-/
lemma neg_v {n : Int} (z : Cochain F G n) (p q : Int) (hpq : p + n = q) :
    (-z).v p q hpq = -(z.v p q hpq) := rfl

@[simp]
/--
lemma `smul_v` / 引理 `smul_v`

English:
lemma smul_v
  given: {n : Int} (k : R) (z : Cochain F G n) (p q : Int) (hpq : p + n = q)
  proof: rfl

@[simp]

中文:
引理 smul_v
  条件: {n : 整数} (k : R) (z : Cochain F G n) (p q : 整数) (hpq : p + n = q)
  证明: rfl

@[simp]
-/
lemma smul_v {n : Int} (k : R) (z : Cochain F G n) (p q : Int) (hpq : p + n = q) :
    (k • z).v p q hpq = k • (z.v p q hpq) := rfl

@[simp]
/--
lemma `units_smul_v` / 引理 `units_smul_v`

English:
lemma units_smul_v
  given: {n : Int} (k : Rˣ) (z : Cochain F G n) (p q : Int) (hpq : p + n = q)
  proof: rfl

中文:
引理 units_smul_v
  条件: {n : 整数} (k : Rˣ) (z : Cochain F G n) (p q : 整数) (hpq : p + n = q)
  证明: rfl
-/
lemma units_smul_v {n : Int} (k : Rˣ) (z : Cochain F G n) (p q : Int) (hpq : p + n = q) :
    (k • z).v p q hpq = k • (z.v p q hpq) := rfl

/--
Definition of `ofHoms` / `ofHoms` 的定义

English:
definition ofHoms
  signature: (ψ : forall (p : Int), F.X p ⟶ G.X p)
  body: Cochain.mk (fun p q hpq => ψ p ≫ eqToHom (by rw [← hpq, add_zero]))

@[simp]

中文:
定义 ofHoms
  签名: (ψ : 对任意 (p : 整数), F.X p ⟶ G.X p)
  定义体: Cochain.mk (fun p q hpq => ψ p ≫ eqToHom (by rw [← hpq, add_zero]))

@[simp]

Depends on / 依赖: Cochain, Cochain.mk, add_zero, eqToHom
-/
def ofHoms (ψ : forall (p : Int), F.X p ⟶ G.X p) : Cochain F G 0 :=
  Cochain.mk (fun p q hpq => ψ p ≫ eqToHom (by rw [← hpq, add_zero]))

@[simp]
/--
lemma `ofHoms_v` / 引理 `ofHoms_v`

English:
lemma ofHoms_v
  given: (ψ : forall (p : Int), F.X p ⟶ G.X p) (p : Int)
  proof: by
  simp only [ofHoms, mk_v, eqToHom_refl, comp_id]

@[simp]

中文:
引理 ofHoms_v
  条件: (ψ : 对任意 (p : 整数), F.X p ⟶ G.X p) (p : 整数)
  证明: by
  simp only [ofHoms, mk_v, eqToHom_refl, comp_id]

@[simp]

Depends on / 依赖: comp_id, eqToHom_refl, mk_v, ofHoms
-/
lemma ofHoms_v (ψ : forall (p : Int), F.X p ⟶ G.X p) (p : Int) :
    (ofHoms ψ).v p p (add_zero p) = ψ p := by
  simp only [ofHoms, mk_v, eqToHom_refl, comp_id]

@[simp]
/--
lemma `ofHoms_zero` / 引理 `ofHoms_zero`

English:
lemma ofHoms_zero
  statement: ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0
  proof: by cat_disch

@[simp]

中文:
引理 ofHoms_zero
  结论: ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma ofHoms_zero : ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0 := by cat_disch

@[simp]
/--
lemma `ofHoms_v_comp_d` / 引理 `ofHoms_v_comp_d`

English:
lemma ofHoms_v_comp_d
  given: (ψ : forall (p : Int), F.X p ⟶ G.X p) (p q q' : Int) (hpq : p + 0 = q)
  proof: by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

@[simp]

中文:
引理 ofHoms_v_comp_d
  条件: (ψ : 对任意 (p : 整数), F.X p ⟶ G.X p) (p q q' : 整数) (hpq : p + 0 = q)
  证明: by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

@[simp]

Depends on / 依赖: add_zero, ofHoms_v
-/
lemma ofHoms_v_comp_d (ψ : forall (p : Int), F.X p ⟶ G.X p) (p q q' : Int) (hpq : p + 0 = q) :
    (ofHoms ψ).v p q hpq ≫ G.d q q' = ψ p ≫ G.d p q' := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

@[simp]
/--
lemma `d_comp_ofHoms_v` / 引理 `d_comp_ofHoms_v`

English:
lemma d_comp_ofHoms_v
  given: (ψ : forall (p : Int), F.X p ⟶ G.X p) (p' p q : Int) (hpq : p + 0 = q)
  proof: by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

中文:
引理 d_comp_ofHoms_v
  条件: (ψ : 对任意 (p : 整数), F.X p ⟶ G.X p) (p' p q : 整数) (hpq : p + 0 = q)
  证明: by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

Depends on / 依赖: add_zero, ofHoms_v
-/
lemma d_comp_ofHoms_v (ψ : forall (p : Int), F.X p ⟶ G.X p) (p' p q : Int) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: (φ : F ⟶ G)
  body: ofHoms (fun p => φ.f p)

中文:
定义 ofHom
  签名: (φ : F ⟶ G)
  定义体: ofHoms (fun p => φ.f p)

Depends on / 依赖: ofHoms
-/
def ofHom (φ : F ⟶ G) : Cochain F G 0 := ofHoms (fun p => φ.f p)

variable (F G)

@[simp]
/--
lemma `ofHom_zero` / 引理 `ofHom_zero`

English:
lemma ofHom_zero
  statement: ofHom (0 : F ⟶ G) = 0
  proof: by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

中文:
引理 ofHom_zero
  结论: ofHom (0 : F ⟶ G) = 0
  证明: by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.zero_f_apply, ofHoms_zero, zero_f_apply
-/
lemma ofHom_zero : ofHom (0 : F ⟶ G) = 0 := by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

variable {F G}

@[simp]
/--
lemma `ofHom_v` / 引理 `ofHom_v`

English:
lemma ofHom_v
  given: (φ : F ⟶ G) (p : Int)
  statement: (ofHom φ).v p p (add_zero p) = φ.f p
  proof: by
  simp only [ofHom, ofHoms_v]

@[simp]

中文:
引理 ofHom_v
  条件: (φ : F ⟶ G) (p : 整数)
  结论: (ofHom φ).v p p (add_zero p) = φ.f p
  证明: by
  simp only [ofHom, ofHoms_v]

@[simp]

Depends on / 依赖: ofHoms_v
-/
lemma ofHom_v (φ : F ⟶ G) (p : Int) : (ofHom φ).v p p (add_zero p) = φ.f p := by
  simp only [ofHom, ofHoms_v]

@[simp]
/--
lemma `ofHom_v_comp_d` / 引理 `ofHom_v_comp_d`

English:
lemma ofHom_v_comp_d
  given: (φ : F ⟶ G) (p q q' : Int) (hpq : p + 0 = q)
  proof: by
  simp only [ofHom, ofHoms_v_comp_d]

@[simp]

中文:
引理 ofHom_v_comp_d
  条件: (φ : F ⟶ G) (p q q' : 整数) (hpq : p + 0 = q)
  证明: by
  simp only [ofHom, ofHoms_v_comp_d]

@[simp]

Depends on / 依赖: ofHoms_v_comp_d
-/
lemma ofHom_v_comp_d (φ : F ⟶ G) (p q q' : Int) (hpq : p + 0 = q) :
    (ofHom φ).v p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q' := by
  simp only [ofHom, ofHoms_v_comp_d]

@[simp]
/--
lemma `d_comp_ofHom_v` / 引理 `d_comp_ofHom_v`

English:
lemma d_comp_ofHom_v
  given: (φ : F ⟶ G) (p' p q : Int) (hpq : p + 0 = q)
  proof: by
  simp only [ofHom, d_comp_ofHoms_v]

@[simp]

中文:
引理 d_comp_ofHom_v
  条件: (φ : F ⟶ G) (p' p q : 整数) (hpq : p + 0 = q)
  证明: by
  simp only [ofHom, d_comp_ofHoms_v]

@[simp]

Depends on / 依赖: d_comp_ofHoms_v
-/
lemma d_comp_ofHom_v (φ : F ⟶ G) (p' p q : Int) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHom φ).v p q hpq = F.d p' q ≫ φ.f q := by
  simp only [ofHom, d_comp_ofHoms_v]

@[simp]
/--
lemma `ofHom_add` / 引理 `ofHom_add`

English:
lemma ofHom_add
  given: (φ₁ φ₂ : F ⟶ G)
  proof: by cat_disch

@[simp]

中文:
引理 ofHom_add
  条件: (φ₁ φ₂ : F ⟶ G)
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma ofHom_add (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ + φ₂) = Cochain.ofHom φ₁ + Cochain.ofHom φ₂ := by cat_disch

@[simp]
/--
lemma `ofHom_sub` / 引理 `ofHom_sub`

English:
lemma ofHom_sub
  given: (φ₁ φ₂ : F ⟶ G)
  proof: by cat_disch

@[simp]

中文:
引理 ofHom_sub
  条件: (φ₁ φ₂ : F ⟶ G)
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma ofHom_sub (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ - φ₂) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by cat_disch

@[simp]
/--
lemma `ofHom_neg` / 引理 `ofHom_neg`

English:
lemma ofHom_neg
  given: (φ : F ⟶ G)
  proof: by cat_disch

中文:
引理 ofHom_neg
  条件: (φ : F ⟶ G)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma ofHom_neg (φ : F ⟶ G) :
    Cochain.ofHom (-φ) = -Cochain.ofHom φ := by cat_disch

/--
Definition of `ofHomotopy` / `ofHomotopy` 的定义

English:
definition ofHomotopy
  signature: {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂)
  body: Cochain.mk (fun p q _ => ho.hom p q)

@[simp]

中文:
定义 ofHomotopy
  签名: {φ₁ φ₂ : F ⟶ G} (ho : 同伦 φ₁ φ₂)
  定义体: Cochain.mk (fun p q _ => ho.hom p q)

@[simp]

Depends on / 依赖: Cochain, Cochain.mk, ho.hom
-/
def ofHomotopy {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂) : Cochain F G (-1) :=
  Cochain.mk (fun p q _ => ho.hom p q)

@[simp]
/--
lemma `ofHomotopy_ofEq` / 引理 `ofHomotopy_ofEq`

English:
lemma ofHomotopy_ofEq
  given: {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂)
  proof: rfl

@[simp]

中文:
引理 ofHomotopy_ofEq
  条件: {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂)
  证明: rfl

@[simp]
-/
lemma ofHomotopy_ofEq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    ofHomotopy (Homotopy.ofEq h) = 0 := rfl

@[simp]
/--
lemma `ofHomotopy_refl` / 引理 `ofHomotopy_refl`

English:
lemma ofHomotopy_refl
  given: (φ : F ⟶ G)
  proof: rfl

@[reassoc]

中文:
引理 ofHomotopy_refl
  条件: (φ : F ⟶ G)
  证明: rfl

@[reassoc]
-/
lemma ofHomotopy_refl (φ : F ⟶ G) :
    ofHomotopy (Homotopy.refl φ) = 0 := rfl

@[reassoc]
/--
lemma `v_comp_XIsoOfEq_hom` / 引理 `v_comp_XIsoOfEq_hom`

English:
lemma v_comp_XIsoOfEq_hom
  proof: by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

@[reassoc]

中文:
引理 v_comp_XIsoOfEq_hom
  证明: by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

@[reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq, Iso.refl_hom, XIsoOfEq, comp_id, eqToIso_refl, refl_hom
-/
lemma v_comp_XIsoOfEq_hom
    (γ : Cochain F G n) (p q q' : Int) (hpq : p + n = q) (hq' : q = q') :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q' (by rw [← hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

@[reassoc]
/--
lemma `v_comp_XIsoOfEq_inv` / 引理 `v_comp_XIsoOfEq_inv`

English:
lemma v_comp_XIsoOfEq_inv
  proof: by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, comp_id]

中文:
引理 v_comp_XIsoOfEq_inv
  证明: by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, comp_id]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq, Iso.refl_inv, XIsoOfEq, comp_id, eqToIso_refl, refl_inv
-/
lemma v_comp_XIsoOfEq_inv
    (γ : Cochain F G n) (p q q' : Int) (hpq : p + n = q) (hq' : q' = q) :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').inv = γ.v p q' (by rw [hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, comp_id]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  body: Cochain.mk (fun p q hpq => z₁.v p (p + n₁) rfl ≫ z₂.v (p + n₁) q (by lia))

中文:
定义 comp
  签名: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  定义体: Cochain.mk (fun p q hpq => z₁.v p (p + n₁) rfl ≫ z₂.v (p + n₁) q (by lia))

Depends on / 依赖: Cochain, Cochain.mk
-/
def comp {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
    Cochain F K n₁₂ :=
  Cochain.mk (fun p q hpq => z₁.v p (p + n₁) rfl ≫ z₂.v (p + n₁) q (by lia))


/--
lemma `comp_v` / 引理 `comp_v`

English:
lemma comp_v
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  proof: by
  subst h₁; rfl

@[simp]

中文:
引理 comp_v
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  证明: by
  subst h₁; rfl

@[simp]
-/
lemma comp_v {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (p₁ p₂ p₃ : Int) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (z₁.comp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  subst h₁; rfl

@[simp]
/--
lemma `comp_zero_cochain_v` / 引理 `comp_zero_cochain_v`

English:
lemma comp_zero_cochain_v
  given: (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q)
  proof: comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

@[simp]

中文:
引理 comp_zero_cochain_v
  条件: (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : 整数) (hpq : p + n = q)
  证明: comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

@[simp]

Depends on / 依赖: add_zero, comp_v
-/
lemma comp_zero_cochain_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) :
    (z₁.comp z₂ (add_zero n)).v p q hpq = z₁.v p q hpq ≫ z₂.v q q (add_zero q) :=
  comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

@[simp]
/--
lemma `zero_cochain_comp_v` / 引理 `zero_cochain_comp_v`

English:
lemma zero_cochain_comp_v
  given: (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q)
  proof: comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

中文:
引理 zero_cochain_comp_v
  条件: (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : 整数) (hpq : p + n = q)
  证明: comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

Depends on / 依赖: add_zero, comp_v, zero_add
-/
lemma zero_cochain_comp_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) :
    (z₁.comp z₂ (zero_add n)).v p q hpq = z₁.v p p (add_zero p) ≫ z₂.v p q hpq :=
  comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : Int}
  proof: by
  subst h₁₂ h₂₃ h₁₂₃
  ext p q hpq
  rw [comp_v _ _ rfl p (p + n₁ + n₂) q (add_assoc _ _ _).symm (by lia)]; rw [comp_v z₁ z₂ rfl p (p + n₁) (p + n₁ + n₂) (by lia) (by lia)]; rw [comp_v z₁ (z₂.comp z₃ rfl) (add_assoc n₁ n₂ n₃).symm p (p + n₁) q (by lia) (by lia)]; rw [comp_v z₂ z₃ rfl (p + n₁) (p 

中文:
引理 comp_assoc
  结论: {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : 整数}
  证明: by
  subst h₁₂ h₂₃ h₁₂₃
  ext p q hpq
  rw [comp_v _ _ rfl p (p + n₁ + n₂) q (add_assoc _ _ _).symm (by lia)]; rw [comp_v z₁ z₂ rfl p (p + n₁) (p + n₁ + n₂) (by lia) (by lia)]; rw [comp_v z₁ (z₂.comp z₃ rfl) (add_assoc n₁ n₂ n₃).symm p (p + n₁) q (by lia) (by lia)]; rw [comp_v z₂ z₃ rfl (p + n₁) (p 

Depends on / 依赖: add_assoc, comp_v
-/
lemma comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : Int}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      z₁.comp (z₂.comp z₃ h₂₃) (by rw [← h₂₃, ← h₁₂₃, add_assoc]) := by
  subst h₁₂ h₂₃ h₁₂₃
  ext p q hpq
  rw [comp_v _ _ rfl p (p + n₁ + n₂) q (add_assoc _ _ _).symm (by lia)]; rw [comp_v z₁ z₂ rfl p (p + n₁) (p + n₁ + n₂) (by lia) (by lia)]; rw [comp_v z₁ (z₂.comp z₃ rfl) (add_assoc n₁ n₂ n₃).symm p (p + n₁) q (by lia) (by lia)]; rw [comp_v z₂ z₃ rfl (p + n₁) (p + n₁ + n₂) q (by lia) (by lia)]; rw [assoc]

/-! The formulation of the associativity of the composition of cochains given by the
lemma `comp_assoc` often requires a careful selection of degrees with good definitional
properties. In a few cases, like when one of the three cochains is a `0`-cochain,
there are better choices, which provides the following simplification lemmas. -/

@[simp]
/--
lemma `comp_assoc_of_first_is_zero_cochain` / 引理 `comp_assoc_of_first_is_zero_cochain`

English:
lemma comp_assoc_of_first_is_zero_cochain
  statement: {n₂ n₃ n₂₃ : Int}
  proof: comp_assoc _ _ _ _ _ (by lia)

@[simp]

中文:
引理 comp_assoc_of_first_is_zero_cochain
  结论: {n₂ n₃ n₂₃ : 整数}
  证明: comp_assoc _ _ _ _ _ (by lia)

@[simp]

Depends on / 依赖: comp_assoc
-/
lemma comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : Int}
    (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₂₃ : n₂ + n₃ = n₂₃) :
    (z₁.comp z₂ (zero_add n₂)).comp z₃ h₂₃ = z₁.comp (z₂.comp z₃ h₂₃) (zero_add n₂₃) :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/--
lemma `comp_assoc_of_second_is_zero_cochain` / 引理 `comp_assoc_of_second_is_zero_cochain`

English:
lemma comp_assoc_of_second_is_zero_cochain
  statement: {n₁ n₃ n₁₃ : Int}
  proof: comp_assoc _ _ _ _ _ (by lia)

@[simp]

中文:
引理 comp_assoc_of_second_is_zero_cochain
  结论: {n₁ n₃ n₁₃ : 整数}
  证明: comp_assoc _ _ _ _ _ (by lia)

@[simp]

Depends on / 依赖: comp_assoc
-/
lemma comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : Int}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃) :
    (z₁.comp z₂ (add_zero n₁)).comp z₃ h₁₃ = z₁.comp (z₂.comp z₃ (zero_add n₃)) h₁₃ :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/--
lemma `comp_assoc_of_third_is_zero_cochain` / 引理 `comp_assoc_of_third_is_zero_cochain`

English:
lemma comp_assoc_of_third_is_zero_cochain
  statement: {n₁ n₂ n₁₂ : Int}
  proof: comp_assoc _ _ _ _ _ (by lia)

@[simp]

中文:
引理 comp_assoc_of_third_is_zero_cochain
  结论: {n₁ n₂ n₁₂ : 整数}
  证明: comp_assoc _ _ _ _ _ (by lia)

@[simp]

Depends on / 依赖: comp_assoc
-/
lemma comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : Int}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃ (add_zero n₁₂) = z₁.comp (z₂.comp z₃ (add_zero n₂)) h₁₂ :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/--
lemma `comp_assoc_of_second_degree_eq_neg_third_degree` / 引理 `comp_assoc_of_second_degree_eq_neg_third_degree`

English:
lemma comp_assoc_of_second_degree_eq_neg_third_degree
  statement: {n₁ n₂ n₁₂ : Int}
  proof: comp_assoc _ _ _ _ _ (by lia)

@[simp]

中文:
引理 comp_assoc_of_second_degree_eq_neg_third_degree
  结论: {n₁ n₂ n₁₂ : 整数}
  证明: comp_assoc _ _ _ _ _ (by lia)

@[simp]

Depends on / 依赖: comp_assoc
-/
lemma comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : Int}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K (-n₂)) (z₃ : Cochain K L n₂) (h₁₂ : n₁ + (-n₂) = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃
      (show n₁₂ + n₂ = n₁ by rw [← h₁₂, add_assoc, neg_add_cancel, add_zero]) =
      z₁.comp (z₂.comp z₃ (neg_add_cancel n₂)) (add_zero n₁) :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/--
lemma `zero_comp` / 引理 `zero_comp`

English:
lemma zero_comp
  statement: {n₁ n₂ n₁₂ : Int} (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, zero_comp]

@[simp]

中文:
引理 zero_comp
  结论: {n₁ n₂ n₁₂ : 整数} (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, zero_comp]

@[simp]
-/
protected lemma zero_comp {n₁ n₂ n₁₂ : Int} (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (0 : Cochain F G n₁).comp z₂ h = 0 := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, zero_comp]

@[simp]
/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  statement: {n₁ n₂ n₁₂ : Int} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, add_comp]

@[simp]

中文:
引理 add_comp
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, add_comp]

@[simp]
-/
protected lemma add_comp {n₁ n₂ n₁₂ : Int} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁ + z₁').comp z₂ h = z₁.comp z₂ h + z₁'.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, add_comp]

@[simp]
/--
lemma `sub_comp` / 引理 `sub_comp`

English:
lemma sub_comp
  statement: {n₁ n₂ n₁₂ : Int} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, sub_comp]

@[simp]

中文:
引理 sub_comp
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, sub_comp]

@[simp]
-/
protected lemma sub_comp {n₁ n₂ n₁₂ : Int} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁ - z₁').comp z₂ h = z₁.comp z₂ h - z₁'.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, sub_comp]

@[simp]
/--
lemma `neg_comp` / 引理 `neg_comp`

English:
lemma neg_comp
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, neg_comp]

@[simp]

中文:
引理 neg_comp
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, neg_comp]

@[simp]
-/
protected lemma neg_comp {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₁).comp z₂ h = -z₁.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, neg_comp]

@[simp]
/--
lemma `smul_comp` / 引理 `smul_comp`

English:
lemma smul_comp
  statement: {n₁ n₂ n₁₂ : Int} (k : R) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.smul_comp]

@[simp]

中文:
引理 smul_comp
  结论: {n₁ n₂ n₁₂ : 整数} (k : R) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.smul_comp]

@[simp]
-/
protected lemma smul_comp {n₁ n₂ n₁₂ : Int} (k : R) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h) := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.smul_comp]

@[simp]
/--
lemma `units_smul_comp` / 引理 `units_smul_comp`

English:
lemma units_smul_comp
  statement: {n₁ n₂ n₁₂ : Int} (k : Rˣ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  proof: by
  apply Cochain.smul_comp

@[simp]

中文:
引理 units_smul_comp
  结论: {n₁ n₂ n₁₂ : 整数} (k : Rˣ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  证明: by
  apply Cochain.smul_comp

@[simp]

Depends on / 依赖: Cochain, Cochain.smul_comp, smul_comp
-/
lemma units_smul_comp {n₁ n₂ n₁₂ : Int} (k : Rˣ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h) := by
  apply Cochain.smul_comp

@[simp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: {n : Int} (z₂ : Cochain F G n)
  proof: by
  ext p q hpq
  simp only [zero_cochain_comp_v, ofHom_v, HomologicalComplex.id_f, id_comp]

@[simp]

中文:
引理 id_comp
  条件: {n : 整数} (z₂ : Cochain F G n)
  证明: by
  ext p q hpq
  simp only [zero_cochain_comp_v, ofHom_v, HomologicalComplex.id_f, id_comp]

@[simp]
-/
protected lemma id_comp {n : Int} (z₂ : Cochain F G n) :
    (Cochain.ofHom (𝟙 F)).comp z₂ (zero_add n) = z₂ := by
  ext p q hpq
  simp only [zero_cochain_comp_v, ofHom_v, HomologicalComplex.id_f, id_comp]

@[simp]
/--
lemma `comp_zero` / 引理 `comp_zero`

English:
lemma comp_zero
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, comp_zero]

@[simp]

中文:
引理 comp_zero
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, comp_zero]

@[simp]
-/
protected lemma comp_zero {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (0 : Cochain G K n₂) h = 0 := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, comp_zero]

@[simp]
/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, comp_add]

@[simp]

中文:
引理 comp_add
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, comp_add]

@[simp]
-/
protected lemma comp_add {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂ + z₂') h = z₁.comp z₂ h + z₁.comp z₂' h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, comp_add]

@[simp]
/--
lemma `comp_sub` / 引理 `comp_sub`

English:
lemma comp_sub
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, comp_sub]

@[simp]

中文:
引理 comp_sub
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, comp_sub]

@[simp]
-/
protected lemma comp_sub {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂ - z₂') h = z₁.comp z₂ h - z₁.comp z₂' h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, comp_sub]

@[simp]
/--
lemma `comp_neg` / 引理 `comp_neg`

English:
lemma comp_neg
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, comp_neg]

@[simp]

中文:
引理 comp_neg
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, comp_neg]

@[simp]
-/
protected lemma comp_neg {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (-z₂) h = -z₁.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, comp_neg]

@[simp]
/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (k : R) (z₂ : Cochain G K n₂)
  proof: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.comp_smul]

@[simp]

中文:
引理 comp_smul
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (k : R) (z₂ : Cochain G K n₂)
  证明: by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.comp_smul]

@[simp]
-/
protected lemma comp_smul {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (k : R) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h) := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.comp_smul]

@[simp]
/--
lemma `comp_units_smul` / 引理 `comp_units_smul`

English:
lemma comp_units_smul
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (k : Rˣ) (z₂ : Cochain G K n₂)
  proof: by
  apply Cochain.comp_smul

@[simp]

中文:
引理 comp_units_smul
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (k : Rˣ) (z₂ : Cochain G K n₂)
  证明: by
  apply Cochain.comp_smul

@[simp]

Depends on / 依赖: Cochain, Cochain.comp_smul, comp_smul
-/
lemma comp_units_smul {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (k : Rˣ) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h) := by
  apply Cochain.comp_smul

@[simp]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: {n : Int} (z₁ : Cochain F G n)
  proof: by
  ext p q hpq
  simp only [comp_zero_cochain_v, ofHom_v, HomologicalComplex.id_f, comp_id]

@[simp]

中文:
引理 comp_id
  条件: {n : 整数} (z₁ : Cochain F G n)
  证明: by
  ext p q hpq
  simp only [comp_zero_cochain_v, ofHom_v, HomologicalComplex.id_f, comp_id]

@[simp]
-/
protected lemma comp_id {n : Int} (z₁ : Cochain F G n) :
    z₁.comp (Cochain.ofHom (𝟙 G)) (add_zero n) = z₁ := by
  ext p q hpq
  simp only [comp_zero_cochain_v, ofHom_v, HomologicalComplex.id_f, comp_id]

@[simp]
/--
lemma `ofHoms_comp` / 引理 `ofHoms_comp`

English:
lemma ofHoms_comp
  given: (φ : forall (p : Int), F.X p ⟶ G.X p) (ψ : forall (p : Int), G.X p ⟶ K.X p)
  proof: by cat_disch

@[simp]

中文:
引理 ofHoms_comp
  条件: (φ : 对任意 (p : 整数), F.X p ⟶ G.X p) (ψ : 对任意 (p : 整数), G.X p ⟶ K.X p)
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma ofHoms_comp (φ : forall (p : Int), F.X p ⟶ G.X p) (ψ : forall (p : Int), G.X p ⟶ K.X p) :
    (ofHoms φ).comp (ofHoms ψ) (zero_add 0) = ofHoms (fun p => φ p ≫ ψ p) := by cat_disch

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  given: (f : F ⟶ G) (g : G ⟶ K)
  proof: by
  simp only [ofHom, HomologicalComplex.comp_f, ofHoms_comp]

中文:
引理 ofHom_comp
  条件: (f : F ⟶ G) (g : G ⟶ K)
  证明: by
  simp only [ofHom, HomologicalComplex.comp_f, ofHoms_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.comp_f, comp_f, ofHoms_comp
-/
lemma ofHom_comp (f : F ⟶ G) (g : G ⟶ K) :
    ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0) := by
  simp only [ofHom, HomologicalComplex.comp_f, ofHoms_comp]

variable (K)

/--
Definition of `diff` / `diff` 的定义

English:
definition diff
  signature: : Cochain K K 1
  body: Cochain.mk (fun p q _ => K.d p q)

@[simp]

中文:
定义 diff
  签名: : Cochain K K 1
  定义体: Cochain.mk (fun p q _ => K.d p q)

@[simp]

Depends on / 依赖: Cochain, Cochain.mk
-/
def diff : Cochain K K 1 := Cochain.mk (fun p q _ => K.d p q)

@[simp]
/--
lemma `diff_v` / 引理 `diff_v`

English:
lemma diff_v
  given: (p q : Int) (hpq : p + 1 = q)
  statement: (diff K).v p q hpq = K.d p q
  proof: rfl

中文:
引理 diff_v
  条件: (p q : 整数) (hpq : p + 1 = q)
  结论: (diff K).v p q hpq = K.d p q
  证明: rfl
-/
lemma diff_v (p q : Int) (hpq : p + 1 = q) : (diff K).v p q hpq = K.d p q := rfl

end Cochain

variable {F G}

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: (z : Cochain F G n)
  body: Cochain.mk (fun p q hpq => z.v p (p + n) rfl ≫ G.d (p + n) q +
    m.negOnePow • F.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel]))

中文:
定义 δ
  签名: (z : Cochain F G n)
  定义体: Cochain.mk (fun p q hpq => z.v p (p + n) rfl ≫ G.d (p + n) q +
    m.negOnePow • F.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel]))

Depends on / 依赖: Cochain, Cochain.mk, m.negOnePow, negOnePow, sub_add_cancel
-/
def δ (z : Cochain F G n) : Cochain F G m :=
  Cochain.mk (fun p q hpq => z.v p (p + n) rfl ≫ G.d (p + n) q +
    m.negOnePow • F.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel]))


/--
lemma `δ_v` / 引理 `δ_v`

English:
lemma δ_v
  statement: (hnm : n + 1 = m) (z : Cochain F G n) (p q : Int) (hpq : p + m = q) (q₁ q₂ : Int)
  proof: by
  obtain rfl : q₁ = p + n := by lia
  obtain rfl : q₂ = p + m - n := by lia
  rfl

中文:
引理 δ_v
  结论: (hnm : n + 1 = m) (z : Cochain F G n) (p q : 整数) (hpq : p + m = q) (q₁ q₂ : 整数)
  证明: by
  obtain rfl : q₁ = p + n := by lia
  obtain rfl : q₂ = p + m - n := by lia
  rfl
-/
lemma δ_v (hnm : n + 1 = m) (z : Cochain F G n) (p q : Int) (hpq : p + m = q) (q₁ q₂ : Int)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) : (δ n m z).v p q hpq =
    z.v p q₁ (by rw [hq₁, ← hpq, ← hnm, ← add_assoc, add_sub_cancel_right]) ≫ G.d q₁ q
      + m.negOnePow • F.d p q₂ ≫ z.v q₂ q
          (by rw [← hq₂, add_assoc, add_comm 1, hnm, hpq]) := by
  obtain rfl : q₁ = p + n := by lia
  obtain rfl : q₂ = p + m - n := by lia
  rfl

/--
lemma `δ_shape` / 引理 `δ_shape`

English:
lemma δ_shape
  given: (hnm : ¬ n + 1 = m) (z : Cochain F G n)
  statement: δ n m z = 0
  proof: by
  ext p q hpq
  dsimp only [δ]
  rw [Cochain.mk_v]; rw [Cochain.zero_v]; rw [F.shape]; rw [G.shape]; rw [comp_zero]; rw [zero_add]; rw [zero_comp]; rw [smul_zero]
  all_goals
    simp only [ComplexShape.up_Rel]
    exact fun _ => hnm (by lia)

中文:
引理 δ_shape
  条件: (hnm : ¬ n + 1 = m) (z : Cochain F G n)
  结论: δ n m z = 0
  证明: by
  ext p q hpq
  dsimp only [δ]
  rw [Cochain.mk_v]; rw [Cochain.zero_v]; rw [F.shape]; rw [G.shape]; rw [comp_zero]; rw [zero_add]; rw [zero_comp]; rw [smul_zero]
  all_goals
    simp only [ComplexShape.up_Rel]
    exact fun _ => hnm (by lia)

Depends on / 依赖: Cochain, Cochain.mk_v, Cochain.zero_v, ComplexShape, ComplexShape.up_Rel, F.shape, G.shape, all_goals, comp_zero, mk_v, smul_zero, up_Rel, zero_add, zero_comp, zero_v
-/
lemma δ_shape (hnm : ¬ n + 1 = m) (z : Cochain F G n) : δ n m z = 0 := by
  ext p q hpq
  dsimp only [δ]
  rw [Cochain.mk_v]; rw [Cochain.zero_v]; rw [F.shape]; rw [G.shape]; rw [comp_zero]; rw [zero_add]; rw [zero_comp]; rw [smul_zero]
  all_goals
    simp only [ComplexShape.up_Rel]
    exact fun _ => hnm (by lia)

variable (F G) (R)

/-- The differential on the complex of morphisms between cochain complexes, as a linear map. -/
@[simps!]
/--
Definition of `δ_hom` / `δ_hom` 的定义

English:
definition δ_hom
  signature: : Cochain F G n ->ₗ[R] Cochain F G m where
  body: δ n m
  map_add' α β := by
    by_cases h : n + 1 = m
    · ext p q hpq
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.add_v, add_comp, comp_add, smul_add]
      abel
    · simp only [δ_shape _ _ h, add_zero]
  map_smul' r a := by
    by_cases h : n + 1 = m
    · ext p q hpq
 

中文:
定义 δ_hom
  签名: : Cochain F G n ->ₗ[R] Cochain F G m where
  定义体: δ n m
  map_add' α β := by
    by_cases h : n + 1 = m
    · ext p q hpq
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.add_v, add_comp, comp_add, smul_add]
      abel
    · simp only [δ_shape _ _ h, add_zero]
  map_smul' r a := by
    by_cases h : n + 1 = m
    · ext p q hpq
 
-/
def δ_hom : Cochain F G n ->ₗ[R] Cochain F G m where
  toFun := δ n m
  map_add' α β := by
    by_cases h : n + 1 = m
    · ext p q hpq
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.add_v, add_comp, comp_add, smul_add]
      abel
    · simp only [δ_shape _ _ h, add_zero]
  map_smul' r a := by
    by_cases h : n + 1 = m
    · ext p q hpq
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.smul_v, Linear.comp_smul,
        Linear.smul_comp, smul_add, smul_comm m.negOnePow r]
    · simp only [δ_shape _ _ h, smul_zero]

variable {F G R}

/--
lemma `δ_add` / 引理 `δ_add`

English:
lemma δ_add
  given: (z₁ z₂ : Cochain F G n)
  statement: δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂
  proof: (δ_hom Int F G n m).map_add z₁ z₂

中文:
引理 δ_add
  条件: (z₁ z₂ : Cochain F G n)
  结论: δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂
  证明: (δ_hom Int F G n m).map_add z₁ z₂
-/
@[simp] lemma δ_add (z₁ z₂ : Cochain F G n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom Int F G n m).map_add z₁ z₂

/--
lemma `δ_sub` / 引理 `δ_sub`

English:
lemma δ_sub
  given: (z₁ z₂ : Cochain F G n)
  statement: δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂
  proof: (δ_hom Int F G n m).map_sub z₁ z₂

中文:
引理 δ_sub
  条件: (z₁ z₂ : Cochain F G n)
  结论: δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂
  证明: (δ_hom Int F G n m).map_sub z₁ z₂
-/
@[simp] lemma δ_sub (z₁ z₂ : Cochain F G n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom Int F G n m).map_sub z₁ z₂

/--
lemma `δ_zero` / 引理 `δ_zero`

English:
lemma δ_zero
  statement: δ n m (0 : Cochain F G n) = 0
  proof: (δ_hom Int F G n m).map_zero

中文:
引理 δ_zero
  结论: δ n m (0 : Cochain F G n) = 0
  证明: (δ_hom Int F G n m).map_zero
-/
@[simp] lemma δ_zero : δ n m (0 : Cochain F G n) = 0 := (δ_hom Int F G n m).map_zero

/--
lemma `δ_neg` / 引理 `δ_neg`

English:
lemma δ_neg
  given: (z : Cochain F G n)
  statement: δ n m (-z) = -δ n m z
  proof: (δ_hom Int F G n m).map_neg z

中文:
引理 δ_neg
  条件: (z : Cochain F G n)
  结论: δ n m (-z) = -δ n m z
  证明: (δ_hom Int F G n m).map_neg z
-/
@[simp] lemma δ_neg (z : Cochain F G n) : δ n m (-z) = -δ n m z :=
  (δ_hom Int F G n m).map_neg z

/--
lemma `δ_smul` / 引理 `δ_smul`

English:
lemma δ_smul
  given: (k : R) (z : Cochain F G n)
  statement: δ n m (k • z) = k • δ n m z
  proof: (δ_hom R F G n m).map_smul k z

中文:
引理 δ_smul
  条件: (k : R) (z : Cochain F G n)
  结论: δ n m (k • z) = k • δ n m z
  证明: (δ_hom R F G n m).map_smul k z
-/
@[simp] lemma δ_smul (k : R) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom R F G n m).map_smul k z

/--
lemma `δ_units_smul` / 引理 `δ_units_smul`

English:
lemma δ_units_smul
  given: (k : Rˣ) (z : Cochain F G n)
  statement: δ n m (k • z) = k • δ n m z
  proof: δ_smul ..

中文:
引理 δ_units_smul
  条件: (k : Rˣ) (z : Cochain F G n)
  结论: δ n m (k • z) = k • δ n m z
  证明: δ_smul ..
-/
@[simp] lemma δ_units_smul (k : Rˣ) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  δ_smul ..

/--
lemma `δ_δ` / 引理 `δ_δ`

English:
lemma δ_δ
  given: (n₀ n₁ n₂ : Int) (z : Cochain F G n₀)
  statement: δ n₁ n₂ (δ n₀ n₁ z) = 0
  proof: by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [δ_shape _ _ h₀₁, δ_zero]
  ext p q hpq
  dsimp
  simp only [δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    δ_v n₀ n₁ h₀₁ z p (q - 1) (by lia) (q - 2) _ (by lia) rfl,
    δ_v n₀ n₁ h₀₁ z (p + 1) q (by 

中文:
引理 δ_δ
  条件: (n₀ n₁ n₂ : 整数) (z : Cochain F G n₀)
  结论: δ n₁ n₂ (δ n₀ n₁ z) = 0
  证明: by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [δ_shape _ _ h₀₁, δ_zero]
  ext p q hpq
  dsimp
  simp only [δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    δ_v n₀ n₁ h₀₁ z p (q - 1) (by lia) (q - 2) _ (by lia) rfl,
    δ_v n₀ n₁ h₀₁ z (p + 1) q (by 

Depends on / 依赖: HomologicalComplex, HomologicalComplex.d_comp_d, HomologicalComplex.d_comp_d_assoc, Int.negOnePow_succ, add_comp, add_neg_cancel, add_zero, comp_add, comp_zero, d_comp_d, d_comp_d_assoc, negOnePow_succ, smul_zero, zero_add, zero_comp
-/
lemma δ_δ (n₀ n₁ n₂ : Int) (z : Cochain F G n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [δ_shape _ _ h₀₁, δ_zero]
  ext p q hpq
  dsimp
  simp only [δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    δ_v n₀ n₁ h₀₁ z p (q - 1) (by lia) (q - 2) _ (by lia) rfl,
    δ_v n₀ n₁ h₀₁ z (p + 1) q (by lia) _ (p + 2) rfl (by lia),
    ← h₁₂, Int.negOnePow_succ, add_comp, assoc,
    HomologicalComplex.d_comp_d, comp_zero, zero_add, comp_add,
    HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero,
    add_zero, add_neg_cancel, Units.neg_smul,
    Linear.units_smul_comp, Linear.comp_units_smul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_comp` / 引理 `δ_comp`

English:
lemma δ_comp
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  proof: by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by lia)]; rw [Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by lia) p (p + n₁ + 1) q
      (by lia) (by lia)]; rw [δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by lia) rfl]; rw [z

中文:
引理 δ_comp
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  证明: by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by lia)]; rw [Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by lia) p (p + n₁ + 1) q
      (by lia) (by lia)]; rw [δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by lia) rfl]; rw [z

Depends on / 依赖: Cochain, Cochain.comp_v, add_assoc, comp_v
-/
lemma δ_comp {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (m₁ m₂ m₁₂ : Int) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (z₁.comp z₂ h) = z₁.comp (δ n₂ m₂ z₂) (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
      n₂.negOnePow • (δ n₁ m₁ z₁).comp z₂
        (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by lia)]; rw [Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by lia) p (p + n₁ + 1) q
      (by lia) (by lia)]; rw [δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by lia) rfl]; rw [z₁.comp_v z₂ rfl p _ _ rfl rfl]; rw [z₁.comp_v z₂ rfl (p + 1) (p + n₁ + 1) q (by lia) (by lia)]; rw [δ_v n₂ (n₂ + 1) rfl z₂ (p + n₁) q (by lia) (p + n₁ + n₂) _ (by lia) rfl]; rw [δ_v n₁ (n₁ + 1) rfl z₁ p (p + n₁ + 1) (by lia) (p + n₁) _ (by lia) rfl]
  simp only [assoc, comp_add, add_comp, Int.negOnePow_succ, Int.negOnePow_add n₁ n₂,
    Units.neg_smul, comp_neg, neg_comp, smul_neg, smul_smul, Linear.units_smul_comp,
    mul_comm n₁.negOnePow n₂.negOnePow, Linear.comp_units_smul, smul_add]
  abel

/--
lemma `δ_zero_cochain_comp` / 引理 `δ_zero_cochain_comp`

English:
lemma δ_zero_cochain_comp
  statement: {n₂ : Int} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
  proof: δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

中文:
引理 δ_zero_cochain_comp
  结论: {n₂ : 整数} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
  证明: δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

Depends on / 依赖: zero_add
-/
lemma δ_zero_cochain_comp {n₂ : Int} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
    (m₂ : Int) (h₂ : n₂ + 1 = m₂) :
    δ n₂ m₂ (z₁.comp z₂ (zero_add n₂)) =
      z₁.comp (δ n₂ m₂ z₂) (zero_add m₂) +
      n₂.negOnePow • ((δ 0 1 z₁).comp z₂ (by rw [add_comm, h₂])) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

/--
lemma `δ_comp_zero_cochain` / 引理 `δ_comp_zero_cochain`

English:
lemma δ_comp_zero_cochain
  statement: {n₁ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
  proof: by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_smul,
    Int.negOnePow_zero]

@[simp]

中文:
引理 δ_comp_zero_cochain
  结论: {n₁ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
  证明: by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_smul,
    Int.negOnePow_zero]

@[simp]

Depends on / 依赖: Int.negOnePow_zero, add_zero, negOnePow_zero, one_smul, zero_add
-/
lemma δ_comp_zero_cochain {n₁ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
    (m₁ : Int) (h₁ : n₁ + 1 = m₁) :
    δ n₁ m₁ (z₁.comp z₂ (add_zero n₁)) =
      z₁.comp (δ 0 1 z₂) h₁ + (δ n₁ m₁ z₁).comp z₂ (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_smul,
    Int.negOnePow_zero]

@[simp]
/--
lemma `δ_zero_cochain_v` / 引理 `δ_zero_cochain_v`

English:
lemma δ_zero_cochain_v
  given: (z : Cochain F G 0) (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by lia) hpq, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_eq_add_neg]

@[simp]

中文:
引理 δ_zero_cochain_v
  条件: (z : Cochain F G 0) (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by lia) hpq, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_eq_add_neg]

@[simp]

Depends on / 依赖: Int.negOnePow_one, Units.neg_smul, negOnePow_one, neg_smul, one_smul, sub_eq_add_neg, zero_add
-/
lemma δ_zero_cochain_v (z : Cochain F G 0) (p q : Int) (hpq : p + 1 = q) :
    (δ 0 1 z).v p q hpq = z.v p p (add_zero p) ≫ G.d p q - F.d p q ≫ z.v q q (add_zero q) := by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by lia) hpq, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_eq_add_neg]

@[simp]
/--
lemma `δ_ofHom` / 引理 `δ_ofHom`

English:
lemma δ_ofHom
  given: {p : Int} (φ : F ⟶ G)
  statement: δ 0 p (Cochain.ofHom φ) = 0
  proof: by
  by_cases h : p = 1
  · subst h
    ext
    simp
  · rw [δ_shape]
    lia

@[simp]

中文:
引理 δ_ofHom
  条件: {p : 整数} (φ : F ⟶ G)
  结论: δ 0 p (Cochain.ofHom φ) = 0
  证明: by
  by_cases h : p = 1
  · subst h
    ext
    simp
  · rw [δ_shape]
    lia

@[simp]
-/
lemma δ_ofHom {p : Int} (φ : F ⟶ G) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : p = 1
  · subst h
    ext
    simp
  · rw [δ_shape]
    lia

@[simp]
/--
lemma `δ_ofHomotopy` / 引理 `δ_ofHomotopy`

English:
lemma δ_ofHomotopy
  given: {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂)
  proof: by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up Int).Rel p (p + 1) by simp)]; rw [prevD_eq h.hom (show (ComplexShape.up Int).Rel (p - 1) p by simp)] at eq
  rw [Cochain.ofHomotopy]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only

中文:
引理 δ_ofHomotopy
  条件: {φ₁ φ₂ : F ⟶ G} (h : 同伦 φ₁ φ₂)
  证明: by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up Int).Rel p (p + 1) by simp)]; rw [prevD_eq h.hom (show (ComplexShape.up Int).Rel (p - 1) p by simp)] at eq
  rw [Cochain.ofHomotopy]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only

Depends on / 依赖: Cochain, Cochain.mk_v, Cochain.ofHom_v, Cochain.ofHomotopy, Cochain.sub_v, ComplexShape, ComplexShape.up, Int.negOnePow_zero, add_zero, dNext_eq, h.comm, h.hom, mk_v, negOnePow_zero, neg_add_cancel, ofHom_v, ofHomotopy, one_smul, prevD_eq, sub_v
-/
lemma δ_ofHomotopy {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up Int).Rel p (p + 1) by simp)]; rw [prevD_eq h.hom (show (ComplexShape.up Int).Rel (p - 1) p by simp)] at eq
  rw [Cochain.ofHomotopy]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [Cochain.mk_v, one_smul, Int.negOnePow_zero, Cochain.sub_v, Cochain.ofHom_v, eq]
  abel

set_option backward.defeqAttrib.useBackward true in
/--
lemma `δ_neg_one_cochain` / 引理 `δ_neg_one_cochain`

English:
lemma δ_neg_one_cochain
  given: (z : Cochain F G (-1))
  proof: by
  ext p
  rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [one_smul, Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up Int).Rel (p - 1) p by simp)
    (show (ComplexShape.up Int).Rel p (p + 1) by simp)]
  abel

中文:
引理 δ_neg_one_cochain
  条件: (z : Cochain F G (-1))
  证明: by
  ext p
  rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [one_smul, Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up Int).Rel (p - 1) p by simp)
    (show (ComplexShape.up Int).Rel p (p + 1) by simp)]
  abel

Depends on / 依赖: Cochain, Cochain.ofHom_v, ComplexShape, ComplexShape.up, Homotopy, Homotopy.nullHomotopicMap, Int.negOnePow_zero, add_zero, negOnePow_zero, neg_add_cancel, nullHomotopicMap, ofHom_v, one_smul
-/
lemma δ_neg_one_cochain (z : Cochain F G (-1)) :
    δ (-1) 0 z = Cochain.ofHom (Homotopy.nullHomotopicMap'
      (fun i j hij => z.v i j (by dsimp at hij; rw [← hij, add_neg_cancel_right]))) := by
  ext p
  rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [one_smul, Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up Int).Rel (p - 1) p by simp)
    (show (ComplexShape.up Int).Rel p (p + 1) by simp)]
  abel

end HomComplex

variable (F G)

open HomComplex

/-- The cochain complex of homomorphisms between two cochain complexes `F` and `G`.
In degree `n : ℤ`, it consists of the abelian group `HomComplex.Cochain F G n`. -/
@[simps! X d_hom_apply]
/--
Definition of `HomComplex` / `HomComplex` 的定义

English:
definition HomComplex
  signature: : CochainComplex AddCommGrpCat Int where
  body: AddCommGrpCat.of (Cochain F G i)
  d i j := AddCommGrpCat.ofHom (δ_hom Int F G i j)
  shape _ _ hij := by ext; simp [δ_shape _ _ hij]
  d_comp_d' _ _ _ _ _ := by ext; simp [δ_δ]

中文:
定义 HomComplex
  签名: : 上链复形 加法交换群范畴 整数 where
  定义体: AddCommGrpCat.of (Cochain F G i)
  d i j := AddCommGrpCat.ofHom (δ_hom Int F G i j)
  shape _ _ hij := by ext; simp [δ_shape _ _ hij]
  d_comp_d' _ _ _ _ _ := by ext; simp [δ_δ]

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, Cochain
-/
def HomComplex : CochainComplex AddCommGrpCat Int where
  X i := AddCommGrpCat.of (Cochain F G i)
  d i j := AddCommGrpCat.ofHom (δ_hom Int F G i j)
  shape _ _ hij := by ext; simp [δ_shape _ _ hij]
  d_comp_d' _ _ _ _ _ := by ext; simp [δ_δ]

namespace HomComplex

/--
Definition of `cocycle` / `cocycle` 的定义

English:
definition cocycle
  signature: : AddSubgroup (Cochain F G n)
  body: AddMonoidHom.ker (δ_hom Int F G n (n + 1)).toAddMonoidHom

中文:
定义 cocycle
  签名: : 加法子群 (Cochain F G n)
  定义体: AddMonoidHom.ker (δ_hom Int F G n (n + 1)).toAddMonoidHom

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ker, toAddMonoidHom
-/
def cocycle : AddSubgroup (Cochain F G n) :=
  AddMonoidHom.ker (δ_hom Int F G n (n + 1)).toAddMonoidHom

/--
Definition of `Cocycle` / `Cocycle` 的定义

English:
definition Cocycle
  signature: : Type v
  body: cocycle F G n

中文:
定义 Cocycle
  签名: : 类型v
  定义体: cocycle F G n

Depends on / 依赖: cocycle
-/
def Cocycle : Type v := cocycle F G n

namespace Cocycle

variable {F G}

/--
lemma `mem_iff` / 引理 `mem_iff`

English:
lemma mem_iff
  given: (hnm : n + 1 = m) (z : Cochain F G n)
  proof: by subst hnm; rfl

中文:
引理 mem_iff
  条件: (hnm : n + 1 = m) (z : Cochain F G n)
  证明: by subst hnm; rfl
-/
lemma mem_iff (hnm : n + 1 = m) (z : Cochain F G n) :
    z in cocycle F G n ↔ δ n m z = 0 := by subst hnm; rfl

variable {n}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Cocycle F G n) (Cochain F G n)
  body: x.1

@[ext]

中文:
实例 :
  签名: Coe (Cocycle F G n) (Cochain F G n)
  定义体: x.1

@[ext]
-/
instance : Coe (Cocycle F G n) (Cochain F G n) where
  coe x := x.1

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {z₁ z₂ : Cocycle F G n} (h : (z₁ : Cochain F G n) = z₂)
  statement: z₁ = z₂
  proof: Subtype.ext h

中文:
引理 ext
  条件: {z₁ z₂ : Cocycle F G n} (h : (z₁ : Cochain F G n) = z₂)
  结论: z₁ = z₂
  证明: Subtype.ext h

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma ext {z₁ z₂ : Cocycle F G n} (h : (z₁ : Cochain F G n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (Cocycle F G n)
  body: ⟨r • z.1, by
    have hz := z.2
    rw [mem_iff n (n + 1) rfl] at hz ⊢
    simp only [δ_smul, hz, smul_zero]⟩

中文:
实例 :
  签名: 标量乘法 R (Cocycle F G n)
  定义体: ⟨r • z.1, by
    have hz := z.2
    rw [mem_iff n (n + 1) rfl] at hz ⊢
    simp only [δ_smul, hz, smul_zero]⟩

Depends on / 依赖: mem_iff, smul_zero
-/
instance : SMul R (Cocycle F G n) where
  smul r z := ⟨r • z.1, by
    have hz := z.2
    rw [mem_iff n (n + 1) rfl] at hz ⊢
    simp only [δ_smul, hz, smul_zero]⟩

variable (F G n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (Cocycle F G n)
  body: inferInstanceAs AddCommGroup (cocycle F G n)

@[simp]

中文:
实例 :
  签名: 加法交换群 (Cocycle F G n)
  定义体: inferInstanceAs AddCommGroup (cocycle F G n)

@[simp]

Depends on / 依赖: AddCommGroup, cocycle
-/
instance : AddCommGroup (Cocycle F G n) :=
inferInstanceAs AddCommGroup (cocycle F G n)

@[simp]
/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: (↑(0 : Cocycle F G n) : Cochain F G n) = 0
  proof: by rfl

中文:
引理 coe_zero
  结论: (↑(0 : Cocycle F G n) : Cochain F G n) = 0
  证明: by rfl
-/
lemma coe_zero : (↑(0 : Cocycle F G n) : Cochain F G n) = 0 := by rfl

variable {F G n}

@[simp]
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (z₁ z₂ : Cocycle F G n)
  proof: rfl

@[simp]

中文:
引理 coe_add
  条件: (z₁ z₂ : Cocycle F G n)
  证明: rfl

@[simp]
-/
lemma coe_add (z₁ z₂ : Cocycle F G n) :
    (↑(z₁ + z₂) : Cochain F G n) = (z₁ : Cochain F G n) + (z₂ : Cochain F G n) := rfl

@[simp]
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (z : Cocycle F G n)
  proof: rfl

@[simp]

中文:
引理 coe_neg
  条件: (z : Cocycle F G n)
  证明: rfl

@[simp]
-/
lemma coe_neg (z : Cocycle F G n) :
    (↑(-z) : Cochain F G n) = -(z : Cochain F G n) := rfl

@[simp]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (z : Cocycle F G n) (x : R)
  proof: rfl

@[simp]

中文:
引理 coe_smul
  条件: (z : Cocycle F G n) (x : R)
  证明: rfl

@[simp]
-/
lemma coe_smul (z : Cocycle F G n) (x : R) :
    (↑(x • z) : Cochain F G n) = x • (z : Cochain F G n) := rfl

@[simp]
/--
lemma `coe_units_smul` / 引理 `coe_units_smul`

English:
lemma coe_units_smul
  given: (z : Cocycle F G n) (x : Rˣ)
  proof: rfl

@[simp]

中文:
引理 coe_units_smul
  条件: (z : Cocycle F G n) (x : Rˣ)
  证明: rfl

@[simp]
-/
lemma coe_units_smul (z : Cocycle F G n) (x : Rˣ) :
    (↑(x • z) : Cochain F G n) = x • (z : Cochain F G n) := rfl

@[simp]
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (z₁ z₂ : Cocycle F G n)
  proof: rfl

中文:
引理 coe_sub
  条件: (z₁ z₂ : Cocycle F G n)
  证明: rfl
-/
lemma coe_sub (z₁ z₂ : Cocycle F G n) :
    (↑(z₁ - z₂) : Cochain F G n) = (z₁ : Cochain F G n) - (z₂ : Cochain F G n) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (Cocycle F G n)
  body: by aesop
  mul_smul _ _ _ := by ext; dsimp; rw [smul_smul]
  smul_zero _ := by aesop
  smul_add _ _ _ := by aesop
  add_smul _ _ _ := by ext; dsimp; rw [add_smul]
  zero_smul := by aesop

中文:
实例 :
  签名: 模 R (Cocycle F G n)
  定义体: by aesop
  mul_smul _ _ _ := by ext; dsimp; rw [smul_smul]
  smul_zero _ := by aesop
  smul_add _ _ _ := by aesop
  add_smul _ _ _ := by ext; dsimp; rw [add_smul]
  zero_smul := by aesop

Depends on / 依赖: add_smul, mul_smul, smul_add, smul_smul, smul_zero, zero_smul
-/
instance : Module R (Cocycle F G n) where
  one_smul _ := by aesop
  mul_smul _ _ _ := by ext; dsimp; rw [smul_smul]
  smul_zero _ := by aesop
  smul_add _ _ _ := by aesop
  add_smul _ _ _ := by ext; dsimp; rw [add_smul]
  zero_smul := by aesop

/-- Constructor for `Cocycle F G n`, taking as inputs `z : Cochain F G n`, an integer
`m : ℤ` such that `n + 1 = m`, and the relation `δ n m z = 0`. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (z : Cochain F G n) (m : Int) (hnm : n + 1 = m) (h : δ n m z = 0)
  body: ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]

中文:
定义 mk
  签名: (z : Cochain F G n) (m : 整数) (hnm : n + 1 = m) (h : δ n m z = 0)
  定义体: ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]

Depends on / 依赖: mem_iff
-/
def mk (z : Cochain F G n) (m : Int) (hnm : n + 1 = m) (h : δ n m z = 0) : Cocycle F G n :=
  ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
/--
lemma `δ_eq_zero` / 引理 `δ_eq_zero`

English:
lemma δ_eq_zero
  given: {n : Int} (z : Cocycle F G n) (m : Int)
  statement: δ n m (z : Cochain F G n) = 0
  proof: by
  by_cases h : n + 1 = m
  · rw [← mem_iff n m h]
    exact z.2
  · exact δ_shape n m h _

中文:
引理 δ_eq_zero
  条件: {n : 整数} (z : Cocycle F G n) (m : 整数)
  结论: δ n m (z : Cochain F G n) = 0
  证明: by
  by_cases h : n + 1 = m
  · rw [← mem_iff n m h]
    exact z.2
  · exact δ_shape n m h _

Depends on / 依赖: mem_iff
-/
lemma δ_eq_zero {n : Int} (z : Cocycle F G n) (m : Int) : δ n m (z : Cochain F G n) = 0 := by
  by_cases h : n + 1 = m
  · rw [← mem_iff n m h]
    exact z.2
  · exact δ_shape n m h _

/-- The `0`-cocycle associated to a morphism in `CochainComplex C ℤ`. -/
@[simps!]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: (φ : F ⟶ G)
  body: mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

中文:
定义 ofHom
  签名: (φ : F ⟶ G)
  定义体: mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

Depends on / 依赖: Cochain, Cochain.ofHom, zero_add
-/
def ofHom (φ : F ⟶ G) : Cocycle F G 0 := mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

/-- The morphism in `CochainComplex C ℤ` associated to a `0`-cocycle. -/
@[simps]
/--
Definition of `homOf` / `homOf` 的定义

English:
definition homOf
  signature: (z : Cocycle F G 0)
  body: (z : Cochain _ _ _).v i i (add_zero i)
  comm' := by
    rintro i j rfl
    rcases z with ⟨z, hz⟩
    dsimp
    rw [mem_iff 0 1 (zero_add 1)] at hz
    simpa only [δ_zero_cochain_v, Cochain.zero_v, sub_eq_zero]
      using Cochain.congr_v hz i (i + 1) rfl

@[simp]

中文:
定义 homOf
  签名: (z : Cocycle F G 0)
  定义体: (z : Cochain _ _ _).v i i (add_zero i)
  comm' := by
    rintro i j rfl
    rcases z with ⟨z, hz⟩
    dsimp
    rw [mem_iff 0 1 (zero_add 1)] at hz
    simpa only [δ_zero_cochain_v, Cochain.zero_v, sub_eq_zero]
      using Cochain.congr_v hz i (i + 1) rfl

@[simp]

Depends on / 依赖: Cochain, add_zero
-/
def homOf (z : Cocycle F G 0) : F ⟶ G where
  f i := (z : Cochain _ _ _).v i i (add_zero i)
  comm' := by
    rintro i j rfl
    rcases z with ⟨z, hz⟩
    dsimp
    rw [mem_iff 0 1 (zero_add 1)] at hz
    simpa only [δ_zero_cochain_v, Cochain.zero_v, sub_eq_zero]
      using Cochain.congr_v hz i (i + 1) rfl

@[simp]
/--
lemma `homOf_ofHom_eq_self` / 引理 `homOf_ofHom_eq_self`

English:
lemma homOf_ofHom_eq_self
  given: (φ : F ⟶ G)
  statement: homOf (ofHom φ) = φ
  proof: by cat_disch

@[simp]

中文:
引理 homOf_ofHom_eq_self
  条件: (φ : F ⟶ G)
  结论: homOf (ofHom φ) = φ
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma homOf_ofHom_eq_self (φ : F ⟶ G) : homOf (ofHom φ) = φ := by cat_disch

@[simp]
/--
lemma `ofHom_homOf_eq_self` / 引理 `ofHom_homOf_eq_self`

English:
lemma ofHom_homOf_eq_self
  given: (z : Cocycle F G 0)
  statement: ofHom (homOf z) = z
  proof: by cat_disch

@[simp]

中文:
引理 ofHom_homOf_eq_self
  条件: (z : Cocycle F G 0)
  结论: ofHom (homOf z) = z
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma ofHom_homOf_eq_self (z : Cocycle F G 0) : ofHom (homOf z) = z := by cat_disch

@[simp]
/--
lemma `cochain_ofHom_homOf_eq_coe` / 引理 `cochain_ofHom_homOf_eq_coe`

English:
lemma cochain_ofHom_homOf_eq_coe
  given: (z : Cocycle F G 0)
  proof: by
  simpa only [Cocycle.ext_iff] using! ofHom_homOf_eq_self z

中文:
引理 cochain_ofHom_homOf_eq_coe
  条件: (z : Cocycle F G 0)
  证明: by
  simpa only [Cocycle.ext_iff] using! ofHom_homOf_eq_self z

Depends on / 依赖: Cocycle, Cocycle.ext_iff, ext_iff, ofHom_homOf_eq_self
-/
lemma cochain_ofHom_homOf_eq_coe (z : Cocycle F G 0) :
    Cochain.ofHom (homOf z) = (z : Cochain F G 0) := by
  simpa only [Cocycle.ext_iff] using! ofHom_homOf_eq_self z

variable (F G)

/-- The additive equivalence between morphisms in `CochainComplex C ℤ` and `0`-cocycles. -/
@[simps]
/--
Definition of `equivHom` / `equivHom` 的定义

English:
definition equivHom
  signature: : (F ⟶ G) ≃+ Cocycle F G 0 where
  body: ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' := by cat_disch

中文:
定义 equivHom
  签名: : (F ⟶ G) ≃+ Cocycle F G 0 where
  定义体: ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' := by cat_disch
-/
def equivHom : (F ⟶ G) ≃+ Cocycle F G 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' := by cat_disch

variable (K)

/-- The `1`-cocycle given by the differential on a cochain complex. -/
@[simps!]
/--
Definition of `diff` / `diff` 的定义

English:
definition diff
  signature: : Cocycle K K 1
  body: Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext p q hpq
    simp only [Cochain.zero_v, δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

中文:
定义 diff
  签名: : Cocycle K K 1
  定义体: Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext p q hpq
    simp only [Cochain.zero_v, δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

Depends on / 依赖: Cochain, Cochain.diff, Cochain.diff_v, Cochain.zero_v, Cocycle, Cocycle.mk, HomologicalComplex, HomologicalComplex.d_comp_d, add_zero, d_comp_d, diff_v, smul_zero, zero_v
-/
def diff : Cocycle K K 1 :=
  Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext p q hpq
    simp only [Cochain.zero_v, δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

variable (L n) in
/-- The inclusion `Cocycle K L n →+ Cochain K L n`. -/
@[simps]
/--
Definition of `toCochainAddMonoidHom` / `toCochainAddMonoidHom` 的定义

English:
definition toCochainAddMonoidHom
  signature: : Cocycle K L n ->+ Cochain K L n where
  body: x
  map_zero' := by simp
  map_add' := by simp

中文:
定义 toCochainAddMonoidHom
  签名: : Cocycle K L n ->+ Cochain K L n where
  定义体: x
  map_zero' := by simp
  map_add' := by simp
-/
def toCochainAddMonoidHom : Cocycle K L n ->+ Cochain K L n where
  toFun x := x
  map_zero' := by simp
  map_add' := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (L n) in
/--
Definition of `isKernel` / `isKernel` 的定义

English:
definition isKernel
  signature: (hm : n + 1 = m)
  body: Fork.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom
      { toFun x := ⟨s.ι x, by
          rw [mem_iff _ _ hm]
          exact ConcreteCategory.congr_hom s.condition x⟩
        map_zero' := by
          #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
          this was 

中文:
定义 isKernel
  签名: (hm : n + 1 = m)
  定义体: Fork.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom
      { toFun x := ⟨s.ι x, by
          rw [mem_iff _ _ hm]
          exact ConcreteCategory.congr_hom s.condition x⟩
        map_zero' := by
          #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
          this was 

Depends on / 依赖: HomComplex
-/
def isKernel (hm : n + 1 = m) :
    IsLimit ((KernelFork.ofι (f := (HomComplex K L).d n m)
      (AddCommGrpCat.ofHom (toCochainAddMonoidHom K L n))) (by cat_disch)) :=
  Fork.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom
      { toFun x := ⟨s.ι x, by
          rw [mem_iff _ _ hm]
          exact ConcreteCategory.congr_hom s.condition x⟩
        map_zero' := by
          #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
          this was just `cat_disch`. -/
          simp +instances only [HomComplex_X, map_zero]
          rfl
        map_add' _ _ := by
          #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
          this was just `cat_disch`. -/
          simp +instances only [HomComplex_X, map_add]
          rfl })
    (by cat_disch) (fun s l hl => by ext : 3; simp [← hl])

end Cocycle

variable {F G}

@[simp]
/--
lemma `δ_comp_zero_cocycle` / 引理 `δ_comp_zero_cocycle`

English:
lemma δ_comp_zero_cocycle
  given: {n : Int} (z₁ : Cochain F G n) (z₂ : Cocycle G K 0) (m : Int)
  proof: by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]

中文:
引理 δ_comp_zero_cocycle
  条件: {n : 整数} (z₁ : Cochain F G n) (z₂ : Cocycle G K 0) (m : 整数)
  证明: by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
-/
lemma δ_comp_zero_cocycle {n : Int} (z₁ : Cochain F G n) (z₂ : Cocycle G K 0) (m : Int) :
    δ n m (z₁.comp z₂.1 (add_zero n)) =
      (δ n m z₁).comp z₂.1 (add_zero m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
/--
lemma `δ_comp_ofHom` / 引理 `δ_comp_ofHom`

English:
lemma δ_comp_ofHom
  given: {n : Int} (z₁ : Cochain F G n) (f : G ⟶ K) (m : Int)
  proof: by
  rw [← Cocycle.ofHom_coe]; rw [δ_comp_zero_cocycle]


@[simp]

中文:
引理 δ_comp_ofHom
  条件: {n : 整数} (z₁ : Cochain F G n) (f : G ⟶ K) (m : 整数)
  证明: by
  rw [← Cocycle.ofHom_coe]; rw [δ_comp_zero_cocycle]


@[simp]

Depends on / 依赖: Cocycle, Cocycle.ofHom_coe, ofHom_coe
-/
lemma δ_comp_ofHom {n : Int} (z₁ : Cochain F G n) (f : G ⟶ K) (m : Int) :
    δ n m (z₁.comp (Cochain.ofHom f) (add_zero n)) =
      (δ n m z₁).comp (Cochain.ofHom f) (add_zero m) := by
  rw [← Cocycle.ofHom_coe]; rw [δ_comp_zero_cocycle]


@[simp]
/--
lemma `δ_zero_cocycle_comp` / 引理 `δ_zero_cocycle_comp`

English:
lemma δ_zero_cocycle_comp
  given: {n : Int} (z₁ : Cocycle F G 0) (z₂ : Cochain G K n) (m : Int)
  proof: by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]

中文:
引理 δ_zero_cocycle_comp
  条件: {n : 整数} (z₁ : Cocycle F G 0) (z₂ : Cochain G K n) (m : 整数)
  证明: by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
-/
lemma δ_zero_cocycle_comp {n : Int} (z₁ : Cocycle F G 0) (z₂ : Cochain G K n) (m : Int) :
    δ n m (z₁.1.comp z₂ (zero_add n)) =
      z₁.1.comp (δ n m z₂) (zero_add m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
/--
lemma `δ_ofHom_comp` / 引理 `δ_ofHom_comp`

English:
lemma δ_ofHom_comp
  given: {n : Int} (f : F ⟶ G) (z : Cochain G K n) (m : Int)
  proof: by
  rw [← Cocycle.ofHom_coe]; rw [δ_zero_cocycle_comp]

中文:
引理 δ_ofHom_comp
  条件: {n : 整数} (f : F ⟶ G) (z : Cochain G K n) (m : 整数)
  证明: by
  rw [← Cocycle.ofHom_coe]; rw [δ_zero_cocycle_comp]

Depends on / 依赖: Cocycle, Cocycle.ofHom_coe, ofHom_coe
-/
lemma δ_ofHom_comp {n : Int} (f : F ⟶ G) (z : Cochain G K n) (m : Int) :
    δ n m ((Cochain.ofHom f).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (δ n m z) (zero_add m) := by
  rw [← Cocycle.ofHom_coe]; rw [δ_zero_cocycle_comp]

/-- The precomposition of a cocycle with a morphism of cochain complexes. -/
@[simps!]
/--
Definition of `Cocycle.precomp` / `Cocycle.precomp` 的定义

English:
definition Cocycle.precomp
  signature: {n : Int} (z : Cocycle G K n) (f : F ⟶ G)
  body: Cocycle.mk ((Cochain.ofHom f).comp z (zero_add n)) _ rfl (by simp)

中文:
定义 Cocycle.precomp
  签名: {n : 整数} (z : Cocycle G K n) (f : F ⟶ G)
  定义体: Cocycle.mk ((Cochain.ofHom f).comp z (zero_add n)) _ rfl (by simp)

Depends on / 依赖: Cochain, Cochain.ofHom, Cocycle, Cocycle.mk, zero_add
-/
def Cocycle.precomp {n : Int} (z : Cocycle G K n) (f : F ⟶ G) : Cocycle F K n :=
  Cocycle.mk ((Cochain.ofHom f).comp z (zero_add n)) _ rfl (by simp)

/-- The postcomposition of a cocycle with a morphism of cochain complexes. -/
@[simps!]
/--
Definition of `Cocycle.postcomp` / `Cocycle.postcomp` 的定义

English:
definition Cocycle.postcomp
  signature: {n : Int} (z : Cocycle F G n) (f : G ⟶ K)
  body: Cocycle.mk (z.1.comp (Cochain.ofHom f) (add_zero n)) _ rfl (by simp)

中文:
定义 Cocycle.postcomp
  签名: {n : 整数} (z : Cocycle F G n) (f : G ⟶ K)
  定义体: Cocycle.mk (z.1.comp (Cochain.ofHom f) (add_zero n)) _ rfl (by simp)

Depends on / 依赖: Cochain, Cochain.ofHom, Cocycle, Cocycle.mk, add_zero
-/
def Cocycle.postcomp {n : Int} (z : Cocycle F G n) (f : G ⟶ K) : Cocycle F K n :=
  Cocycle.mk (z.1.comp (Cochain.ofHom f) (add_zero n)) _ rfl (by simp)

namespace Cochain

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given two morphisms of complexes `φ₁ φ₂ : F ⟶ G`, the datum of a homotopy between `φ₁` and
`φ₂` is equivalent to the datum of a `1`-cochain `z` such that `δ (-1) 0 z` is the difference
of the zero cochains associated to `φ₂` and `φ₁`. -/
@[simps]
/--
Definition of `equivHomotopy` / `equivHomotopy` 的定义

English:
definition equivHomotopy
  signature: (φ₁ φ₂ : F ⟶ G)
  body: ⟨Cochain.ofHomotopy ho, by simp only [δ_ofHomotopy, sub_add_cancel]⟩
  invFun z :=
    { hom := fun i j => if hij : i + (-1) = j then z.1.v i j hij else 0
      zero := fun i j (hij : j + 1 != i) => dif_neg (fun _ => hij (by lia))
      comm := fun p => by
        have eq := Cochain.congr_v z.2 p p 

中文:
定义 equivHomotopy
  签名: (φ₁ φ₂ : F ⟶ G)
  定义体: ⟨Cochain.ofHomotopy ho, by simp only [δ_ofHomotopy, sub_add_cancel]⟩
  invFun z :=
    { hom := fun i j => if hij : i + (-1) = j then z.1.v i j hij else 0
      zero := fun i j (hij : j + 1 != i) => dif_neg (fun _ => hij (by lia))
      comm := fun p => by
        have eq := Cochain.congr_v z.2 p p 

Depends on / 依赖: Cochain, Cochain.ofHomotopy, ofHomotopy, sub_add_cancel
-/
def equivHomotopy (φ₁ φ₂ : F ⟶ G) :
    Homotopy φ₁ φ₂ ≃
      { z : Cochain F G (-1) // Cochain.ofHom φ₁ = δ (-1) 0 z + Cochain.ofHom φ₂ } where
  toFun ho := ⟨Cochain.ofHomotopy ho, by simp only [δ_ofHomotopy, sub_add_cancel]⟩
  invFun z :=
    { hom := fun i j => if hij : i + (-1) = j then z.1.v i j hij else 0
      zero := fun i j (hij : j + 1 != i) => dif_neg (fun _ => hij (by lia))
      comm := fun p => by
        have eq := Cochain.congr_v z.2 p p (add_zero p)
        have h₁ : (ComplexShape.up Int).Rel (p - 1) p := by simp
        have h₂ : (ComplexShape.up Int).Rel p (p + 1) := by simp
        simp only [δ_neg_one_cochain, Cochain.ofHom_v, ComplexShape.up_Rel, Cochain.add_v,
          Homotopy.nullHomotopicMap'_f h₁ h₂] at eq
        rw [dNext_eq _ h₂]; rw [prevD_eq _ h₁]; rw [eq]; rw [dif_pos]; rw [dif_pos] }
  left_inv := fun ho => by
    ext i j
    dsimp
    split_ifs with h
    · rfl
    · rw [ho.zero i j (fun h' => h (by dsimp at h'; lia))]
  right_inv := fun z => by
    ext p q hpq
    dsimp [Cochain.ofHomotopy]
    rw [dif_pos hpq]

@[simp]
/--
lemma `equivHomotopy_apply_of_eq` / 引理 `equivHomotopy_apply_of_eq`

English:
lemma equivHomotopy_apply_of_eq
  given: {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂)
  proof: rfl

中文:
引理 equivHomotopy_apply_of_eq
  条件: {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂)
  证明: rfl
-/
lemma equivHomotopy_apply_of_eq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    (equivHomotopy _ _ (Homotopy.ofEq h)).1 = 0 := rfl

/--
lemma `ofHom_injective` / 引理 `ofHom_injective`

English:
lemma ofHom_injective
  given: {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂)
  statement: f₁ = f₂
  proof: (Cocycle.equivHom F G).injective (by ext1; exact h)

中文:
引理 ofHom_injective
  条件: {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂)
  结论: f₁ = f₂
  证明: (Cocycle.equivHom F G).injective (by ext1; exact h)

Depends on / 依赖: Cocycle, Cocycle.equivHom, equivHom, injective
-/
lemma ofHom_injective {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂) : f₁ = f₂ :=
  (Cocycle.equivHom F G).injective (by ext1; exact h)

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: {p q : Int} (f : K.X p ⟶ L.X q) (n : Int)
  body: Cochain.mk (fun p' q' _ =>
    if h : p = p' ∧ q = q'
      then (K.XIsoOfEq h.1).inv ≫ f ≫ (L.XIsoOfEq h.2).hom
      else 0)

中文:
定义 single
  签名: {p q : 整数} (f : K.X p ⟶ L.X q) (n : 整数)
  定义体: Cochain.mk (fun p' q' _ =>
    if h : p = p' ∧ q = q'
      then (K.XIsoOfEq h.1).inv ≫ f ≫ (L.XIsoOfEq h.2).hom
      else 0)

Depends on / 依赖: Cochain, Cochain.mk, K.XIsoOfEq, L.XIsoOfEq, XIsoOfEq
-/
def single {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) :
    Cochain K L n :=
  Cochain.mk (fun p' q' _ =>
    if h : p = p' ∧ q = q'
      then (K.XIsoOfEq h.1).inv ≫ f ≫ (L.XIsoOfEq h.2).hom
      else 0)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `single_v` / 引理 `single_v`

English:
lemma single_v
  given: {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (hpq : p + n = q)
  proof: by
  dsimp [single]
  rw [if_pos]; rw [id_comp]; rw [comp_id]
  tauto

中文:
引理 single_v
  条件: {p q : 整数} (f : K.X p ⟶ L.X q) (n : 整数) (hpq : p + n = q)
  证明: by
  dsimp [single]
  rw [if_pos]; rw [id_comp]; rw [comp_id]
  tauto

Depends on / 依赖: comp_id, id_comp, if_pos, single
-/
lemma single_v {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (hpq : p + n = q) :
    (single f n).v p q hpq = f := by
  dsimp [single]
  rw [if_pos]; rw [id_comp]; rw [comp_id]
  tauto

/--
lemma `single_v_eq_zero` / 引理 `single_v_eq_zero`

English:
lemma single_v_eq_zero
  statement: {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q')
  proof: by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hp' (by lia)

中文:
引理 single_v_eq_zero
  结论: {p q : 整数} (f : K.X p ⟶ L.X q) (n : 整数) (p' q' : 整数) (hpq' : p' + n = q')
  证明: by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hp' (by lia)

Depends on / 依赖: dif_neg, single
-/
lemma single_v_eq_zero {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q')
    (hp' : p' != p) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hp' (by lia)

/--
lemma `single_v_eq_zero'` / 引理 `single_v_eq_zero'`

English:
lemma single_v_eq_zero'
  statement: {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q')
  proof: by
  dsimp [single]
  grind

中文:
引理 single_v_eq_zero'
  结论: {p q : 整数} (f : K.X p ⟶ L.X q) (n : 整数) (p' q' : 整数) (hpq' : p' + n = q')
  证明: by
  dsimp [single]
  grind

Depends on / 依赖: single
-/
lemma single_v_eq_zero' {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q')
    (hq' : q' != q) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  grind

variable (K L) in
@[simp]
/--
lemma `single_zero` / 引理 `single_zero`

English:
lemma single_zero
  given: (p q n : Int)
  proof: by
  ext p' q' hpq'
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq
      simp
    · simp [single_v_eq_zero' _ _ _ _ _ hq]
  · simp [single_v_eq_zero _ _ _ _ _ hp]

中文:
引理 single_zero
  条件: (p q n : 整数)
  证明: by
  ext p' q' hpq'
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq
      simp
    · simp [single_v_eq_zero' _ _ _ _ _ hq]
  · simp [single_v_eq_zero _ _ _ _ _ hp]

Depends on / 依赖: Cochain, single_v_eq_zero
-/
lemma single_zero (p q n : Int) :
    (single (p := p) (q := q) 0 n : Cochain K L n) = 0 := by
  ext p' q' hpq'
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq
      simp
    · simp [single_v_eq_zero' _ _ _ _ _ hq]
  · simp [single_v_eq_zero _ _ _ _ _ hp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_single` / 引理 `δ_single`

English:
lemma δ_single
  statement: {p q : Int} (f : K.X p ⟶ L.X q) (n m : Int) (hm : n + 1 = m)
  proof: by
  ext p'' q'' hpq''
  rw [δ_v n m hm (single f n) p'' q'' (by lia) (q'' - 1) (p'' + 1) rfl (by lia)]; rw [add_v]; rw [units_smul_v]
  congr 1
  · by_cases h : p'' = p
    · subst h
      by_cases h : q = q'' - 1
      · subst h
        obtain rfl : q' = q'' := by lia
        simp only [single_v]


中文:
引理 δ_single
  结论: {p q : 整数} (f : K.X p ⟶ L.X q) (n m : 整数) (hm : n + 1 = m)
  证明: by
  ext p'' q'' hpq''
  rw [δ_v n m hm (single f n) p'' q'' (by lia) (q'' - 1) (p'' + 1) rfl (by lia)]; rw [add_v]; rw [units_smul_v]
  congr 1
  · by_cases h : p'' = p
    · subst h
      by_cases h : q = q'' - 1
      · subst h
        obtain rfl : q' = q'' := by lia
        simp only [single_v]


Depends on / 依赖: add_v, all_goals, single, single_v, single_v_eq_zero, units_smul_v, zero_comp
-/
lemma δ_single {p q : Int} (f : K.X p ⟶ L.X q) (n m : Int) (hm : n + 1 = m)
    (p' q' : Int) (hp' : p' + 1 = p) (hq' : q + 1 = q') :
    δ n m (single f n) = single (f ≫ L.d q q') m + m.negOnePow • single (K.d p' p ≫ f) m := by
  ext p'' q'' hpq''
  rw [δ_v n m hm (single f n) p'' q'' (by lia) (q'' - 1) (p'' + 1) rfl (by lia)]; rw [add_v]; rw [units_smul_v]
  congr 1
  · by_cases h : p'' = p
    · subst h
      by_cases h : q = q'' - 1
      · subst h
        obtain rfl : q' = q'' := by lia
        simp only [single_v]
      · rw [single_v_eq_zero', single_v_eq_zero', zero_comp]
        all_goals lia
    · rw [single_v_eq_zero _ _ _ _ _ h, single_v_eq_zero _ _ _ _ _ h, zero_comp]
  · subst hm
    by_cases h : q'' = q
    · subst h
      by_cases h : p'' = p'
      · subst h
        obtain rfl : p = p'' + 1 := by lia
        simp
      · rw [single_v_eq_zero _ _ _ _ _ h, single_v_eq_zero, comp_zero, smul_zero]
        lia
    · simp [single_v_eq_zero' _ _ _ _ _ h]

end Cochain

section

variable {n} {D : Type*} [Category* D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

namespace Cochain

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n
  body: Cochain.mk (fun p q hpq => Φ.map (z.v p q hpq))

@[simp]

中文:
定义 map
  签名: : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n
  定义体: Cochain.mk (fun p q hpq => Φ.map (z.v p q hpq))

@[simp]

Depends on / 依赖: Cochain, Cochain.mk
-/
def map : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cochain.mk (fun p q hpq => Φ.map (z.v p q hpq))

@[simp]
/--
lemma `map_v` / 引理 `map_v`

English:
lemma map_v
  given: (p q : Int) (hpq : p + n = q)
  statement: (z.map Φ).v p q hpq = Φ.map (z.v p q hpq)
  proof: rfl

@[simp]

中文:
引理 map_v
  条件: (p q : 整数) (hpq : p + n = q)
  结论: (z.map Φ).v p q hpq = Φ.map (z.v p q hpq)
  证明: rfl

@[simp]
-/
lemma map_v (p q : Int) (hpq : p + n = q) : (z.map Φ).v p q hpq = Φ.map (z.v p q hpq) := rfl

@[simp]
/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  statement: (z + z').map Φ = z.map Φ + z'.map Φ
  proof: by cat_disch

@[simp]

中文:
引理 map_add
  结论: (z + z').map Φ = z.map Φ + z'.map Φ
  证明: by cat_disch

@[simp]
-/
protected lemma map_add : (z + z').map Φ = z.map Φ + z'.map Φ := by cat_disch

@[simp]
/--
lemma `map_neg` / 引理 `map_neg`

English:
lemma map_neg
  statement: (-z).map Φ = -z.map Φ
  proof: by cat_disch

@[simp]

中文:
引理 map_neg
  结论: (-z).map Φ = -z.map Φ
  证明: by cat_disch

@[simp]
-/
protected lemma map_neg : (-z).map Φ = -z.map Φ := by cat_disch

@[simp]
/--
lemma `map_sub` / 引理 `map_sub`

English:
lemma map_sub
  statement: (z - z').map Φ = z.map Φ - z'.map Φ
  proof: by cat_disch

中文:
引理 map_sub
  结论: (z - z').map Φ = z.map Φ - z'.map Φ
  证明: by cat_disch
-/
protected lemma map_sub : (z - z').map Φ = z.map Φ - z'.map Φ := by cat_disch

variable (K L n)

@[simp]
/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  statement: (0 : Cochain K L n).map Φ = 0
  proof: by cat_disch

中文:
引理 map_zero
  结论: (0 : Cochain K L n).map Φ = 0
  证明: by cat_disch
-/
protected lemma map_zero : (0 : Cochain K L n).map Φ = 0 := by cat_disch

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  proof: by
  ext p q hpq
  dsimp
  simp only [map_v, comp_v _ _ h p _ q rfl (by lia), Φ.map_comp]

@[simp]

中文:
引理 map_comp
  结论: {n₁ n₂ n₁₂ : 整数} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
  证明: by
  ext p q hpq
  dsimp
  simp only [map_v, comp_v _ _ h p _ q rfl (by lia), Φ.map_comp]

@[simp]

Depends on / 依赖: comp_v, map_comp, map_v
-/
lemma map_comp {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (Φ : C ⥤ D) [Φ.Additive] :
    (Cochain.comp z₁ z₂ h).map Φ = Cochain.comp (z₁.map Φ) (z₂.map Φ) h := by
  ext p q hpq
  dsimp
  simp only [map_v, comp_v _ _ h p _ q rfl (by lia), Φ.map_comp]

@[simp]
/--
lemma `map_ofHom` / 引理 `map_ofHom`

English:
lemma map_ofHom
  proof: by cat_disch

中文:
引理 map_ofHom
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma map_ofHom :
    (Cochain.ofHom f).map Φ = Cochain.ofHom ((Φ.mapHomologicalComplex _).map f) := by cat_disch

end Cochain

variable (n)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `δ_map` / 引理 `δ_map`

English:
lemma δ_map
  statement: δ n m (z.map Φ) = (δ n m z).map Φ
  proof: by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      Functor.map_add, Functor.map_comp, Functor.map_units_smul,
      Cochain.map_v, Functor.mapHomologicalComplex_obj_d]
  · simp only [δ_shape _ _ hnm, Cochain.map_zero]

中文:
引理 δ_map
  结论: δ n m (z.map Φ) = (δ n m z).map Φ
  证明: by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      Functor.map_add, Functor.map_comp, Functor.map_units_smul,
      Cochain.map_v, Functor.mapHomologicalComplex_obj_d]
  · simp only [δ_shape _ _ hnm, Cochain.map_zero]

Depends on / 依赖: Cochain, Cochain.map_v, Cochain.map_zero, Functor, Functor.mapHomologicalComplex_obj_d, Functor.map_add, Functor.map_comp, Functor.map_units_smul, mapHomologicalComplex_obj_d, map_add, map_comp, map_units_smul, map_v, map_zero
-/
lemma δ_map : δ n m (z.map Φ) = (δ n m z).map Φ := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      Functor.map_add, Functor.map_comp, Functor.map_units_smul,
      Cochain.map_v, Functor.mapHomologicalComplex_obj_d]
  · simp only [δ_shape _ _ hnm, Cochain.map_zero]

end

end HomComplex

end CochainComplex
