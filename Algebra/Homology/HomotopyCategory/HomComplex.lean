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

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

namespace HomComplex

/-- A term of type `HomComplex.Triplet n` consists of two integers `p` and `q`
such that `p + n = q`. (This type is introduced so that the instance
`AddCommGroup (Cochain F G n)` defined below can be found automatically.) -/
/-
**CochainComplex.HomComplex.Triplet** 是 Mathlib 中的一个归纳类型，位于命名空间 `CochainComplex.
HomComplex`。
形式化陈述：ℤ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term of type `HomComplex.Triplet n` consists of two integers `p` and `q`
such that `p + n = q`. (This type is introduced so that the instance
`AddCommGroup (Cochain F G n)` defined below can be found automatically.)
-/
structure Triplet (n : ℤ) where
  /-- a first integer -/
  p : ℤ
  /-- a second integer -/
  q : ℤ
  /-- the condition on the two integers -/
  hpq : p + n = q

variable (F G)

/-- A cochain of degree `n : ℤ` between two cochain complexes `F` and `G` consists
of a family of morphisms `F.X p ⟶ G.X q` whenever `p + n = q`, i.e. for all
triplets in `HomComplex.Triplet n`. -/
/-
**CochainComplex.HomComplex.Cochain** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Ho
mComplex`。
形式化陈述：Cochain
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cochain of degree `n : ℤ` between two cochain complexes `F` and `G` consists
of a family of morphisms `F.X p ⟶ G.X q` whenever `p + n = q`, i.e. for all
triplets in `HomComplex.Triplet n`.
-/
def Cochain := ∀ (T : Triplet n), F.X T.p ⟶ G.X T.q

namespace Cochain

-- The `SMul` instance exists to avoid a zsmul diamond.
deriving instance SMul R, AddCommGroup, Module R for Cochain F G n

variable {F G n}

/-- A practical constructor for cochains. -/
/-
**CochainComplex.HomComplex.Cochain.mk** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex
.HomComplex.Cochain`。
形式化陈述：mk (v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q) : Cochain F G n
参数：v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A practical constructor for cochains.
-/
def mk (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) : Cochain F G n :=
  fun ⟨p, q, hpq⟩ => v p q hpq

/-- The value of a cochain on a triplet `⟨p, q, hpq⟩`. -/
/-
**CochainComplex.HomComplex.Cochain.v** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.
HomComplex.Cochain`。
形式化陈述：v (γ : Cochain F G n) (p q : Int) (hpq : p + n = q) : F.X p ⟶ G.X q
参数：γ : Cochain F G n；p q : Int；hpq : p + n = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value of a cochain on a triplet `⟨p, q, hpq⟩`.
-/
def v (γ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    F.X p ⟶ G.X q := γ ⟨p, q, hpq⟩

@[simp]
/-
**CochainComplex.HomComplex.Cochain.mk_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.HomComplex.Cochain`。
形式化陈述：mk_v (v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q) (p q : Int) (
hpq : p + n = q) : (Cochain.mk v).v p q hpq = v p q hpq
参数：v : forall (p q : Int) (_ : p + n = q), F.X p ⟶ G.X q；p q : Int；hpq : p + n =
 q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma mk_v (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) (p q : ℤ) (hpq : p + n = q) :
    (Cochain.mk v).v p q hpq = v p q hpq := rfl
/-
**CochainComplex.HomComplex.Cochain.congr_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：congr_v {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q
) : z₁.v p q hpq = z₂.v p q hpq
参数：h : z₁ = z₂；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma congr_v {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : ℤ) (hpq : p + n = q) :
    z₁.v p q hpq = z₂.v p q hpq := by subst h; rfl

@[ext]
/-
**CochainComplex.HomComplex.Cochain.ext** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.HomComplex.Cochain`。
形式化陈述：ext (z₁ z₂ : Cochain F G n) (h : forall (p q hpq), z₁.v p q hpq = z₂.v p q
 hpq) : z₁ = z₂
参数：z₁ z₂ : Cochain F G n；h : forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext (z₁ z₂ : Cochain F G n)
    (h : ∀ (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂ := by
  funext ⟨p, q, hpq⟩
  apply h

@[ext 1100]
/-
**CochainComplex.HomComplex.Cochain.ext** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.HomComplex.Cochain`。
形式化陈述：ext (z₁ z₂ : Cochain F G n) (h : forall (p q hpq), z₁.v p q hpq = z₂.v p q
 hpq) : z₁ = z₂
参数：z₁ z₂ : Cochain F G n；h : forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext₀ (z₁ z₂ : Cochain F G 0)
    (h : ∀ (p : ℤ), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂ := by
  ext
  grind

@[simp]
/-
**CochainComplex.HomComplex.Cochain.zero_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：zero_v {n : Int} (p q : Int) (hpq : p + n = q) : (0 : Cochain F G n).v p q
 hpq = 0
参数：p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma zero_v {n : ℤ} (p q : ℤ) (hpq : p + n = q) :
    (0 : Cochain F G n).v p q hpq = 0 := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.add_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.HomComplex.Cochain`。
形式化陈述：add_v {n : Int} (z₁ z₂ : Cochain F G n) (p q : Int) (hpq : p + n = q) : (z
₁ + z₂).v p q hpq = z₁.v p q hpq + z₂.v p q hpq
参数：z₁ z₂ : Cochain F G n；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma add_v {n : ℤ} (z₁ z₂ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (z₁ + z₂).v p q hpq = z₁.v p q hpq + z₂.v p q hpq := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.sub_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.HomComplex.Cochain`。
形式化陈述：sub_v {n : Int} (z₁ z₂ : Cochain F G n) (p q : Int) (hpq : p + n = q) : (z
₁ - z₂).v p q hpq = z₁.v p q hpq - z₂.v p q hpq
参数：z₁ z₂ : Cochain F G n；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma sub_v {n : ℤ} (z₁ z₂ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (z₁ - z₂).v p q hpq = z₁.v p q hpq - z₂.v p q hpq := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.neg_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.HomComplex.Cochain`。
形式化陈述：neg_v {n : Int} (z : Cochain F G n) (p q : Int) (hpq : p + n = q) : (-z).v
 p q hpq = -(z.v p q hpq)
参数：z : Cochain F G n；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma neg_v {n : ℤ} (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (-z).v p q hpq = -(z.v p q hpq) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.smul_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：smul_v {n : Int} (k : R) (z : Cochain F G n) (p q : Int) (hpq : p + n = q)
 : (k • z).v p q hpq = k • (z.v p q hpq)
参数：k : R；z : Cochain F G n；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma smul_v {n : ℤ} (k : R) (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (k • z).v p q hpq = k • (z.v p q hpq) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.units_smul_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.HomComplex.Cochain`。
形式化陈述：units_smul_v {n : Int} (k : Rˣ) (z : Cochain F G n) (p q : Int) (hpq : p +
 n = q) : (k • z).v p q hpq = k • (z.v p q hpq)
参数：k : Rˣ；z : Cochain F G n；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma units_smul_v {n : ℤ} (k : Rˣ) (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (k • z).v p q hpq = k • (z.v p q hpq) := rfl

/-- A cochain of degree `0` from `F` to `G` can be constructed from a family
of morphisms `F.X p ⟶ G.X p` for all `p : ℤ`. -/
/-
**CochainComplex.HomComplex.Cochain.ofHoms** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：ofHoms (ψ : forall (p : Int), F.X p ⟶ G.X p) : Cochain F G 0
参数：ψ : forall (p : Int), F.X p ⟶ G.X p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cochain of degree `0` from `F` to `G` can be constructed from a family
of morphisms `F.X p ⟶ G.X p` for all `p : ℤ`.
-/
def ofHoms (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) : Cochain F G 0 :=
  Cochain.mk (fun p q hpq => ψ p ≫ eqToHom (by rw [← hpq, add_zero]))

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHoms_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：ofHoms_v (ψ : forall (p : Int), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p 
p (add_zero p) = ψ p
参数：ψ : forall (p : Int), F.X p ⟶ G.X p；p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p : ℤ) :
    (ofHoms ψ).v p p (add_zero p) = ψ p := by
  simp only [ofHoms, mk_v, eqToHom_refl, comp_id]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHoms_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.HomComplex.Cochain`。
形式化陈述：ofHoms_zero : ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHoms_zero : ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0 := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHoms_v_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：ofHoms_v_comp_d (ψ : forall (p : Int), F.X p ⟶ G.X p) (p q q' : Int) (hpq 
: p + 0 = q) : (ofHoms ψ).v p q hpq ≫ G.d q q' = ψ p ≫ G.d p q'
参数：ψ : forall (p : Int), F.X p ⟶ G.X p；p q q' : Int；hpq : p + 0 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
-/
lemma ofHoms_v_comp_d (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p q q' : ℤ) (hpq : p + 0 = q) :
    (ofHoms ψ).v p q hpq ≫ G.d q q' = ψ p ≫ G.d p q' := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.d_comp_ofHoms_v** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：d_comp_ofHoms_v (ψ : forall (p : Int), F.X p ⟶ G.X p) (p' p q : Int) (hpq 
: p + 0 = q) : F.d p' p ≫ (ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q
参数：ψ : forall (p : Int), F.X p ⟶ G.X p；p' p q : Int；hpq : p + 0 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
-/
lemma d_comp_ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p' p q : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

/-- The `0`-cochain attached to a morphism of cochain complexes. -/
/-
**CochainComplex.HomComplex.Cochain.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.HomComplex.Cochain`。
形式化陈述：ofHom (φ : F ⟶ G) : Cochain F G 0
参数：φ : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `0`-cochain attached to a morphism of cochain complexes.
-/
def ofHom (φ : F ⟶ G) : Cochain F G 0 := ofHoms (fun p => φ.f p)

variable (F G)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：ofHom_zero : ofHom (0 : F ⟶ G) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_zero`：ofHoms_zero : ofHoms (fun
 p => (0 : F.X p ⟶ G.X p)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_zero : ofHom (0 : F ⟶ G) = 0 := by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

variable {F G}

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：ofHom_v (φ : F ⟶ G) (p : Int) : (ofHom φ).v p p (add_zero p) = φ.f p
参数：φ : F ⟶ G；p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_v (φ : F ⟶ G) (p : ℤ) : (ofHom φ).v p p (add_zero p) = φ.f p := by
  simp only [ofHom, ofHoms_v]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_v_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：ofHom_v_comp_d (φ : F ⟶ G) (p q q' : Int) (hpq : p + 0 = q) : (ofHom φ).v 
p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q'
参数：φ : F ⟶ G；p q q' : Int；hpq : p + 0 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v_comp_d`：ofHoms_v_comp_d (ψ : 
forall (p : Int), F.X p ⟶ G.X p) (p q q' : Int) (hpq : p + 0 = q) : (ofHoms ψ).v
 p q hpq ≫ G.d q q' = ψ p ≫ G.d p q'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_v_comp_d (φ : F ⟶ G) (p q q' : ℤ) (hpq : p + 0 = q) :
    (ofHom φ).v p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q' := by
  simp only [ofHom, ofHoms_v_comp_d]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.d_comp_ofHom_v** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：d_comp_ofHom_v (φ : F ⟶ G) (p' p q : Int) (hpq : p + 0 = q) : F.d p' p ≫ (
ofHom φ).v p q hpq = F.d p' q ≫ φ.f q
参数：φ : F ⟶ G；p' p q : Int；hpq : p + 0 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.d_comp_ofHoms_v`：d_comp_ofHoms_v (ψ : 
forall (p : Int), F.X p ⟶ G.X p) (p' p q : Int) (hpq : p + 0 = q) : F.d p' p ≫ (
ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_comp_ofHom_v (φ : F ⟶ G) (p' p q : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHom φ).v p q hpq = F.d p' q ≫ φ.f q := by
  simp only [ofHom, d_comp_ofHoms_v]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_add** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：ofHom_add (φ₁ φ₂ : F ⟶ G) : Cochain.ofHom (φ₁ + φ₂) = Cochain.ofHom φ₁ + C
ochain.ofHom φ₂
参数：φ₁ φ₂ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_add (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ + φ₂) = Cochain.ofHom φ₁ + Cochain.ofHom φ₂ := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_sub** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：ofHom_sub (φ₁ φ₂ : F ⟶ G) : Cochain.ofHom (φ₁ - φ₂) = Cochain.ofHom φ₁ - C
ochain.ofHom φ₂
参数：φ₁ φ₂ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_sub (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ - φ₂) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_neg** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：ofHom_neg (φ : F ⟶ G) : Cochain.ofHom (-φ) = -Cochain.ofHom φ
参数：φ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_neg (φ : F ⟶ G) :
    Cochain.ofHom (-φ) = -Cochain.ofHom φ := by cat_disch

/-- The cochain of degree `-1` given by a homotopy between two morphisms of complexes. -/
/-
**CochainComplex.HomComplex.Cochain.ofHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：ofHomotopy {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂) : Cochain F G (-1)
参数：ho : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cochain of degree `-1` given by a homotopy between two morphisms of complexe
s.
-/
def ofHomotopy {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂) : Cochain F G (-1) :=
  Cochain.mk (fun p q _ => ho.hom p q)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHomotopy_ofEq** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：ofHomotopy_ofEq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) : ofHomotopy (Homotopy.ofEq 
h) = 0
参数：h : φ₁ = φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma ofHomotopy_ofEq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    ofHomotopy (Homotopy.ofEq h) = 0 := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHomotopy_refl** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：ofHomotopy_refl (φ : F ⟶ G) : ofHomotopy (Homotopy.refl φ) = 0
参数：φ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma ofHomotopy_refl (φ : F ⟶ G) :
    ofHomotopy (Homotopy.refl φ) = 0 := rfl

@[reassoc]
/-
**CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：v_comp_XIsoOfEq_hom (γ : Cochain F G n) (p q q' : Int) (hpq : p + n = q) (
hq' : q = q') : γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q'
 (by rw [← hq', hpq])
参数：γ : Cochain F G n；p q q' : Int；hpq : p + n = q；hq' : q = q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma v_comp_XIsoOfEq_hom
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q = q') :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q' (by rw [← hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

@[reassoc]
/-
**CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_inv** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：v_comp_XIsoOfEq_inv (γ : Cochain F G n) (p q q' : Int) (hpq : p + n = q) (
hq' : q' = q) : γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').inv = γ.v p q'
 (by rw [hq', hpq])
参数：γ : Cochain F G n；p q q' : Int；hpq : p + n = q；hq' : q' = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma v_comp_XIsoOfEq_inv
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q' = q) :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').inv = γ.v p q' (by rw [hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, comp_id]

/-- The composition of cochains. -/
/-
**CochainComplex.HomComplex.Cochain.comp** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.HomComplex.Cochain`。
形式化陈述：comp {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁
 + n₂ = n₁₂) : Cochain F K n₁₂
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K n₂；h : n₁ + n₂ = n₁₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of cochains.
-/
def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
    Cochain F K n₁₂ :=
  Cochain.mk (fun p q hpq => z₁.v p (p + n₁) rfl ≫ z₂.v (p + n₁) q (by lia))

/-! If `z₁` is a cochain of degree `n₁` and `z₂` is a cochain of degree `n₂`, and we
have a relation `h : n₁ + n₂ = n₁₂`, then `z₁.comp z₂ h` is a cochain of degree `n₁₂`.
The following lemma `comp_v` computes the value of this composition `z₁.comp z₂ h`
on a triplet `⟨p₁, p₃, _⟩` (with `p₁ + n₁₂ = p₃`). In order to use this lemma,
we need to provide an intermediate integer `p₂` such that `p₁ + n₁ = p₂`.
It is advisable to use a `p₂` that has good definitional properties
(i.e. `p₁ + n₁` is not always the best choice.)

When `z₁` or `z₂` is a `0`-cochain, there is a better choice of `p₂`, and this leads
to the two simplification lemmas `comp_zero_cochain_v` and `zero_cochain_comp_v`.

-/

/-
**CochainComplex.HomComplex.Cochain.comp_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：comp_v {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : 
n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) : (z₁.co
mp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) = z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ 
p₃ h₂
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K n₂；h : n₁ + n₂ = n₁₂；p₁ p₂ p₃ : Int；h₁ :
 p₁ + n₁ = p₂；h₂ : p₂ + n₂ = p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
If `z₁` is a cochain of degree `n₁` and `z₂` is a cochain of degree `n₂`, and we
have a relation `h : n₁ + n₂ = n₁₂`, then `z₁.comp z₂ h` is a cochain of degree 
`n₁₂`.
The following lemma `comp_v` computes the value of this composition `z₁.comp z₂ 
h`
on a triplet `⟨p₁, p₃, _⟩` (with `p₁ + n₁₂ = p₃`). In order to use this lemma,
we need to provide an intermediate integer `p₂` such that `p₁ + n₁ = p₂`.
It is advisable to use a `p₂` that has good definitional properties
(i.e. `p₁ + n₁` is not always the best choice.)

When `z₁` or `z₂` is a `0`-cochain, there is a better choice of `p₂`, and this l
eads
to the two simplification lemmas `comp_zero_cochain_v` and `zero_cochain_comp_v`
.
-/
lemma comp_v {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (p₁ p₂ p₃ : ℤ) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (z₁.comp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  subst h₁; rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_zero_cochain_v** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：comp_zero_cochain_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) 
(hpq : p + n = q) : (z₁.comp z₂ (add_zero n)).v p q hpq = z₁.v p q hpq ≫ z₂.v q 
q (add_zero q)
参数：z₁ : Cochain F G n；z₂ : Cochain G K 0；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma comp_zero_cochain_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (add_zero n)).v p q hpq = z₁.v p q hpq ≫ z₂.v q q (add_zero q) :=
  comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.zero_cochain_comp_v** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：zero_cochain_comp_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) 
(hpq : p + n = q) : (z₁.comp z₂ (zero_add n)).v p q hpq = z₁.v p p (add_zero p) 
≫ z₂.v p q hpq
参数：z₁ : Cochain F G 0；z₂ : Cochain G K n；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma zero_cochain_comp_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (zero_add n)).v p q hpq = z₁.v p p (add_zero p) ≫ z₂.v p q hpq :=
  comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

/-- The associativity of the composition of cochains. -/
/-
**CochainComplex.HomComplex.Cochain.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : Int} (z₁ : Cochain F G n₁) (z₂ : Cocha
in G K n₂) (z₃ : Cochain K L n₃) (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁
₂₃ : n₁ + n₂ + n₃ = n₁₂₃) : (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₃ = n₁₂₃ by rw
 [← h₁₂, h₁₂₃]) = z₁.comp (z₂.comp z₃ h₂₃) (by rw [← h₂₃, ← h₁₂₃, add_assoc])
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K n₂；z₃ : Cochain K L n₃；h₁₂ : n₁ + n₂ = n
₁₂；h₂₃ : n₂ + n₃ = n₂₃；h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
The associativity of the composition of cochains.
-/
lemma comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      z₁.comp (z₂.comp z₃ h₂₃) (by rw [← h₂₃, ← h₁₂₃, add_assoc]) := by
  subst h₁₂ h₂₃ h₁₂₃
  ext p q hpq
  rw [comp_v _ _ rfl p (p + n₁ + n₂) q (add_assoc _ _ _).symm (by lia),
    comp_v z₁ z₂ rfl p (p + n₁) (p + n₁ + n₂) (by lia) (by lia),
    comp_v z₁ (z₂.comp z₃ rfl) (add_assoc n₁ n₂ n₃).symm p (p + n₁) q (by lia) (by lia),
    comp_v z₂ z₃ rfl (p + n₁) (p + n₁ + n₂) q (by lia) (by lia), assoc]

/-! The formulation of the associativity of the composition of cochains given by the
lemma `comp_assoc` often requires a careful selection of degrees with good definitional
properties. In a few cases, like when one of the three cochains is a `0`-cochain,
there are better choices, which provides the following simplification lemmas. -/

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain** 是 Math
lib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : Int} (z₁ : Cochain F G 0)
 (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃) (h₂₃ : n₂ + n₃ = n₂₃) : (z₁.comp z₂
 (zero_add n₂)).comp z₃ h₂₃ = z₁.comp (z₂.comp z₃ h₂₃) (zero_add n₂₃)
参数：z₁ : Cochain F G 0；z₂ : Cochain G K n₂；z₃ : Cochain K L n₃；h₂₃ : n₂ + n₃ = n₂
₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc`：comp_assoc {n₁ n₂ n₃ n₁₂ n
₂₃ n₁₂₃ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
 (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ +…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
The formulation of the associativity of the composition of cochains given by the
lemma `comp_assoc` often requires a careful selection of degrees with good defin
itional
properties. In a few cases, like when one of the three cochains is a `0`-cochain
,
there are better choices, which provides the following simplification lemmas.
-/
lemma comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : ℤ}
    (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₂₃ : n₂ + n₃ = n₂₃) :
    (z₁.comp z₂ (zero_add n₂)).comp z₃ h₂₃ = z₁.comp (z₂.comp z₃ h₂₃) (zero_add n₂₃) :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain** 是 Mat
hlib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : Int} (z₁ : Cochain F G n
₁) (z₂ : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃) : (z₁.comp z
₂ (add_zero n₁)).comp z₃ h₁₃ = z₁.comp (z₂.comp z₃ (zero_add n₃)) h₁₃
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K 0；z₃ : Cochain K L n₃；h₁₃ : n₁ + n₃ = n₁
₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc`：comp_assoc {n₁ n₂ n₃ n₁₂ n
₂₃ n₁₂₃ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
 (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ +…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃) :
    (z₁.comp z₂ (add_zero n₁)).comp z₃ h₁₃ = z₁.comp (z₂.comp z₃ (zero_add n₃)) h₁₃ :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_assoc_of_third_is_zero_cochain** 是 Math
lib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁
) (z₂ : Cochain G K n₂) (z₃ : Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂) : (z₁.comp z₂
 h₁₂).comp z₃ (add_zero n₁₂) = z₁.comp (z₂.comp z₃ (add_zero n₂)) h₁₂
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K n₂；z₃ : Cochain K L 0；h₁₂ : n₁ + n₂ = n₁
₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc`：comp_assoc {n₁ n₂ n₃ n₁₂ n
₂₃ n₁₂₃ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
 (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ +…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃ (add_zero n₁₂) = z₁.comp (z₂.comp z₃ (add_zero n₂)) h₁₂ :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_assoc_of_second_degree_eq_neg_third_deg
ree** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : Int} (z₁ : Co
chain F G n₁) (z₂ : Cochain G K (-n₂)) (z₃ : Cochain K L n₂) (h₁₂ : n₁ + (-n₂) =
 n₁₂) : (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₂ = n₁ by rw [← h₁₂, add_assoc, ne
g_add_cancel, add_zero]) = z₁.comp (z₂.comp z₃ (neg_add_cancel n₂)) (add_zero n₁
)
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K (-n₂)；z₃ : Cochain K L n₂；h₁₂ : n₁ + (-n
₂) = n₁₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc`：comp_assoc {n₁ n₂ n₃ n₁₂ n
₂₃ n₁₂₃ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
 (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ +…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
lemma comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K (-n₂)) (z₃ : Cochain K L n₂) (h₁₂ : n₁ + (-n₂) = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃
      (show n₁₂ + n₂ = n₁ by rw [← h₁₂, add_assoc, neg_add_cancel, add_zero]) =
      z₁.comp (z₂.comp z₃ (neg_add_cancel n₂)) (add_zero n₁) :=
  comp_assoc _ _ _ _ _ (by lia)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₂ : Coch
ainComplex.HomComplex.Cochain G K n₂) (h : n₁ + n₂ = n₁₂),   CochainComplex.HomC
omplex.Cochain.comp 0 z₂ h = 0
参数：z₂ : CochainComplex.HomComplex.Cochain G K n₂；h : n₁ + n₂ = n₁₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma zero_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (0 : Cochain F G n₁).comp z₂ h = 0 := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, zero_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.add_comp** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : 
CochainComplex.HomComplex.Cochain F G n₁)   (z₂ : CochainComplex.HomComplex.Coch
ain G K n₂) (h : n₁ + n₂ = n₁₂),   (z₁ + z₁').comp z₂ h = z₁.comp z₂ h + z₁'.com
p z₂ h
参数：z₁ z₁' : CochainComplex.HomComplex.Cochain F G n₁；z₂ : CochainComplex.HomComp
lex.Cochain G K n₂；h : n₁ + n₂ = n₁₂；z₁ + z₁'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁ + z₁').comp z₂ h = z₁.comp z₂ h + z₁'.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, add_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.sub_comp** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : 
CochainComplex.HomComplex.Cochain F G n₁)   (z₂ : CochainComplex.HomComplex.Coch
ain G K n₂) (h : n₁ + n₂ = n₁₂),   (z₁ - z₁').comp z₂ h = z₁.comp z₂ h - z₁'.com
p z₂ h
参数：z₁ z₁' : CochainComplex.HomComplex.Cochain F G n₁；z₂ : CochainComplex.HomComp
lex.Cochain G K n₂；h : n₁ + n₂ = n₁₂；z₁ - z₁'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁ - z₁').comp z₂ h = z₁.comp z₂ h - z₁'.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, sub_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.neg_comp** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : Coch
ainComplex.HomComplex.Cochain F G n₁)   (z₂ : CochainComplex.HomComplex.Cochain 
G K n₂) (h : n₁ + n₂ = n₁₂), (-z₁).comp z₂ h = -z₁.comp z₂ h
参数：z₁ : CochainComplex.HomComplex.Cochain F G n₁；z₂ : CochainComplex.HomComplex.
Cochain G K n₂；h : n₁ + n₂ = n₁₂；-z₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₁).comp z₂ h = -z₁.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, neg_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {R : Type u_1}   [inst_2 : Ring R] [inst_3 : CategoryTheo
ry.Linear R C] {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (k : R)   (z₁ : Coch
ainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G 
K n₂) (h : n₁ + n₂ = n₁₂),   (k • z₁).comp z₂ h = k • z₁.comp z₂ h
参数：k : R；z₁ : CochainComplex.HomComplex.Cochain F G n₁；z₂ : CochainComplex.HomCo
mplex.Cochain G K n₂；h : n₁ + n₂ = n₁₂；k • z₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma smul_comp {n₁ n₂ n₁₂ : ℤ} (k : R) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h) := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.smul_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.units_smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：units_smul_comp {n₁ n₂ n₁₂ : Int} (k : Rˣ) (z₁ : Cochain F G n₁) (z₂ : Coc
hain G K n₂) (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h)
参数：k : Rˣ；z₁ : Cochain F G n₁；z₂ : Cochain G K n₂；h : n₁ + n₂ = n₁₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CochainComplex.HomComplex.Cochain.smul_comp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {R : Type 
u_1}   [inst_2 : Ring R] [inst_3 …
-/
lemma units_smul_comp {n₁ n₂ n₁₂ : ℤ} (k : Rˣ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h) := by
  apply Cochain.smul_comp

@[simp]
/-
**CochainComplex.HomComplex.Cochain.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G : CochainComplex C ℤ} {n : ℤ} (z₂ : CochainComplex
.HomComplex.Cochain F G n),   (CochainComplex.HomComplex.Cochain.ofHom (Category
Theory.CategoryStruct.id F)).comp z₂ ⋯ = z₂
参数：z₂ : CochainComplex.HomComplex.Cochain F G n；CochainComplex.HomComplex.Cochai
n.ofHom (CategoryTheory.CategoryStruct.id F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma id_comp {n : ℤ} (z₂ : Cochain F G n) :
    (Cochain.ofHom (𝟙 F)).comp z₂ (zero_add n) = z₂ := by
  ext p q hpq
  simp only [zero_cochain_comp_v, ofHom_v, HomologicalComplex.id_f, id_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : Coch
ainComplex.HomComplex.Cochain F G n₁) (h : n₁ + n₂ = n₁₂),   z₁.comp 0 h = 0
参数：z₁ : CochainComplex.HomComplex.Cochain F G n₁；h : n₁ + n₂ = n₁₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma comp_zero {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (0 : Cochain G K n₂) h = 0 := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), zero_v, comp_zero]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_add** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : Coch
ainComplex.HomComplex.Cochain F G n₁)   (z₂ z₂' : CochainComplex.HomComplex.Coch
ain G K n₂) (h : n₁ + n₂ = n₁₂),   z₁.comp (z₂ + z₂') h = z₁.comp z₂ h + z₁.comp
 z₂' h
参数：z₁ : CochainComplex.HomComplex.Cochain F G n₁；z₂ z₂' : CochainComplex.HomComp
lex.Cochain G K n₂；h : n₁ + n₂ = n₁₂；z₂ + z₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂ + z₂') h = z₁.comp z₂ h + z₁.comp z₂' h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), add_v, comp_add]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : Coch
ainComplex.HomComplex.Cochain F G n₁)   (z₂ z₂' : CochainComplex.HomComplex.Coch
ain G K n₂) (h : n₁ + n₂ = n₁₂),   z₁.comp (z₂ - z₂') h = z₁.comp z₂ h - z₁.comp
 z₂' h
参数：z₁ : CochainComplex.HomComplex.Cochain F G n₁；z₂ z₂' : CochainComplex.HomComp
lex.Cochain G K n₂；h : n₁ + n₂ = n₁₂；z₂ - z₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂ - z₂') h = z₁.comp z₂ h - z₁.comp z₂' h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), sub_v, comp_sub]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : Coch
ainComplex.HomComplex.Cochain F G n₁)   (z₂ : CochainComplex.HomComplex.Cochain 
G K n₂) (h : n₁ + n₂ = n₁₂), z₁.comp (-z₂) h = -z₁.comp z₂ h
参数：z₁ : CochainComplex.HomComplex.Cochain F G n₁；z₂ : CochainComplex.HomComplex.
Cochain G K n₂；h : n₁ + n₂ = n₁₂；-z₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (-z₂) h = -z₁.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), neg_v, comp_neg]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {R : Type u_1}   [inst_2 : Ring R] [inst_3 : CategoryTheo
ry.Linear R C] {F G K : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ}   (z₁ : CochainCompl
ex.HomComplex.Cochain F G n₁) (k : R) (z₂ : CochainComplex.HomComplex.Cochain G 
K n₂)   (h : n₁ + n₂ = n₁₂), z₁.comp (k • z₂) h = k • z₁.comp z₂ h
参数：z₁ : CochainComplex.HomComplex.Cochain F G n₁；k : R；z₂ : CochainComplex.HomCo
mplex.Cochain G K n₂；h : n₁ + n₂ = n₁₂；k • z₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma comp_smul {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (k : R) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h) := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by lia), smul_v, Linear.comp_smul]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_units_smul** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：comp_units_smul {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (k : Rˣ) (z₂ : Coc
hain G K n₂) (h : n₁ + n₂ = n₁₂) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h)
参数：z₁ : Cochain F G n₁；k : Rˣ；z₂ : Cochain G K n₂；h : n₁ + n₂ = n₁₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_smul`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {R : Type 
u_1}   [inst_2 : Ring R] [inst_3 …
-/
lemma comp_units_smul {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (k : Rˣ) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h) := by
  apply Cochain.comp_smul

@[simp]
/-
**CochainComplex.HomComplex.Cochain.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {F G : CochainComplex C ℤ} {n : ℤ} (z₁ : CochainComplex
.HomComplex.Cochain F G n),   z₁.comp (CochainComplex.HomComplex.Cochain.ofHom (
CategoryTheory.CategoryStruct.id G)) ⋯ = z₁
参数：z₁ : CochainComplex.HomComplex.Cochain F G n；CochainComplex.HomComplex.Cochai
n.ofHom (CategoryTheory.CategoryStruct.id G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma comp_id {n : ℤ} (z₁ : Cochain F G n) :
    z₁.comp (Cochain.ofHom (𝟙 G)) (add_zero n) = z₁ := by
  ext p q hpq
  simp only [comp_zero_cochain_v, ofHom_v, HomologicalComplex.id_f, comp_id]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHoms_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.HomComplex.Cochain`。
形式化陈述：ofHoms_comp (φ : forall (p : Int), F.X p ⟶ G.X p) (ψ : forall (p : Int), G
.X p ⟶ K.X p) : (ofHoms φ).comp (ofHoms ψ) (zero_add 0) = ofHoms (fun p => φ p ≫
 ψ p)
参数：φ : forall (p : Int), F.X p ⟶ G.X p；ψ : forall (p : Int), G.X p ⟶ K.X p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHoms_comp (φ : ∀ (p : ℤ), F.X p ⟶ G.X p) (ψ : ∀ (p : ℤ), G.X p ⟶ K.X p) :
    (ofHoms φ).comp (ofHoms ψ) (zero_add 0) = ofHoms (fun p => φ p ≫ ψ p) := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cochain.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：ofHom_comp (f : F ⟶ G) (g : G ⟶ K) : ofHom (f ≫ g) = (ofHom f).comp (ofHom
 g) (zero_add 0)
参数：f : F ⟶ G；g : G ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_comp`：ofHoms_comp (φ : forall (
p : Int), F.X p ⟶ G.X p) (ψ : forall (p : Int), G.X p ⟶ K.X p) : (ofHoms φ).comp
 (ofHoms ψ) (zero_add 0) = ofHoms (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_comp (f : F ⟶ G) (g : G ⟶ K) :
    ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0) := by
  simp only [ofHom, HomologicalComplex.comp_f, ofHoms_comp]

variable (K)

/-- The differential on a cochain complex, as a cochain of degree `1`. -/
/-
**CochainComplex.HomComplex.Cochain.diff** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.HomComplex.Cochain`。
形式化陈述：diff : Cochain K K 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential on a cochain complex, as a cochain of degree `1`.
-/
def diff : Cochain K K 1 := Cochain.mk (fun p q _ => K.d p q)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.diff_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：diff_v (p q : Int) (hpq : p + 1 = q) : (diff K).v p q hpq = K.d p q
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma diff_v (p q : ℤ) (hpq : p + 1 = q) : (diff K).v p q hpq = K.d p q := rfl

end Cochain

variable {F G}

/-- The differential on the complex of morphisms between cochain complexes. -/
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential on the complex of morphisms between cochain complexes.
-/
def δ (z : Cochain F G n) : Cochain F G m :=
  Cochain.mk (fun p q hpq => z.v p (p + n) rfl ≫ G.d (p + n) q +
    m.negOnePow • F.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel]))

/-! Similarly as for the composition of cochains, if `z : Cochain F G n`,
we usually need to carefully select intermediate indices with
good definitional properties in order to obtain a suitable expansion of the
morphisms which constitute `δ n m z : Cochain F G m` (when `n + 1 = m`, otherwise
it shall be zero). The basic equational lemma is `δ_v` below. -/

/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Similarly as for the composition of cochains, if `z : Cochain F G n`,
we usually need to carefully select intermediate indices with
good definitional properties in order to obtain a suitable expansion of the
morphisms which constitute `δ n m z : Cochain F G m` (when `n + 1 = m`, otherwis
e
it shall be zero). The basic equational lemma is `δ_v` below.
-/
lemma δ_v (hnm : n + 1 = m) (z : Cochain F G n) (p q : ℤ) (hpq : p + m = q) (q₁ q₂ : ℤ)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) : (δ n m z).v p q hpq =
    z.v p q₁ (by rw [hq₁, ← hpq, ← hnm, ← add_assoc, add_sub_cancel_right]) ≫ G.d q₁ q
      + m.negOnePow • F.d p q₂ ≫ z.v q₂ q
          (by rw [← hq₂, add_assoc, add_comm 1, hnm, hpq]) := by
  obtain rfl : q₁ = p + n := by lia
  obtain rfl : q₂ = p + m - n := by lia
  rfl
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_shape (hnm : ¬ n + 1 = m) (z : Cochain F G n) : δ n m z = 0 := by
  ext p q hpq
  dsimp only [δ]
  rw [Cochain.mk_v, Cochain.zero_v, F.shape, G.shape, comp_zero, zero_add, zero_comp, smul_zero]
  all_goals
    simp only [ComplexShape.up_Rel]
    exact fun _ => hnm (by lia)

variable (F G) (R)

/-- The differential on the complex of morphisms between cochain complexes, as a linear map. -/
@[simps!]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential on the complex of morphisms between cochain complexes, as a lin
ear map.
-/
def δ_hom : Cochain F G n →ₗ[R] Cochain F G m where
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
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma δ_add (z₁ z₂ : Cochain F G n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom ℤ F G n m).map_add z₁ z₂
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma δ_sub (z₁ z₂ : Cochain F G n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom ℤ F G n m).map_sub z₁ z₂
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma δ_zero : δ n m (0 : Cochain F G n) = 0 := (δ_hom ℤ F G n m).map_zero
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma δ_neg (z : Cochain F G n) : δ n m (-z) = -δ n m z :=
  (δ_hom ℤ F G n m).map_neg z
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma δ_smul (k : R) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom R F G n m).map_smul k z
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma δ_units_smul (k : Rˣ) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  δ_smul ..
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_δ (n₀ n₁ n₂ : ℤ) (z : Cochain F G n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
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
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (z₁.comp z₂ h) = z₁.comp (δ n₂ m₂ z₂) (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
      n₂.negOnePow • (δ n₁ m₁ z₁).comp z₂
        (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by lia),
    Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by lia) p (p + n₁ + 1) q
      (by lia) (by lia),
    δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by lia) rfl,
    z₁.comp_v z₂ rfl p _ _ rfl rfl,
    z₁.comp_v z₂ rfl (p + 1) (p + n₁ + 1) q (by lia) (by lia),
    δ_v n₂ (n₂ + 1) rfl z₂ (p + n₁) q (by lia) (p + n₁ + n₂) _ (by lia) rfl,
    δ_v n₁ (n₁ + 1) rfl z₁ p (p + n₁ + 1) (by lia) (p + n₁) _ (by lia) rfl]
  simp only [assoc, comp_add, add_comp, Int.negOnePow_succ, Int.negOnePow_add n₁ n₂,
    Units.neg_smul, comp_neg, neg_comp, smul_neg, smul_smul, Linear.units_smul_comp,
    mul_comm n₁.negOnePow n₂.negOnePow, Linear.comp_units_smul, smul_add]
  abel
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
    (m₂ : ℤ) (h₂ : n₂ + 1 = m₂) :
    δ n₂ m₂ (z₁.comp z₂ (zero_add n₂)) =
      z₁.comp (δ n₂ m₂ z₂) (zero_add m₂) +
      n₂.negOnePow • ((δ 0 1 z₁).comp z₂ (by rw [add_comm, h₂])) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) :
    δ n₁ m₁ (z₁.comp z₂ (add_zero n₁)) =
      z₁.comp (δ 0 1 z₂) h₁ + (δ n₁ m₁ z₁).comp z₂ (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_smul,
    Int.negOnePow_zero]

@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_cochain_v (z : Cochain F G 0) (p q : ℤ) (hpq : p + 1 = q) :
    (δ 0 1 z).v p q hpq = z.v p p (add_zero p) ≫ G.d p q - F.d p q ≫ z.v q q (add_zero q) := by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by lia) hpq, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_eq_add_neg]

@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_ofHom {p : ℤ} (φ : F ⟶ G) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : p = 1
  · subst h
    ext
    simp
  · rw [δ_shape]
    lia

@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_ofHomotopy {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at eq
  rw [Cochain.ofHomotopy, δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [Cochain.mk_v, one_smul, Int.negOnePow_zero, Cochain.sub_v, Cochain.ofHom_v, eq]
  abel

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_neg_one_cochain (z : Cochain F G (-1)) :
    δ (-1) 0 z = Cochain.ofHom (Homotopy.nullHomotopicMap'
      (fun i j hij => z.v i j (by dsimp at hij; rw [← hij, add_neg_cancel_right]))) := by
  ext p
  rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [one_smul, Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)
    (show (ComplexShape.up ℤ).Rel p (p + 1) by simp)]
  abel

end HomComplex

variable (F G)

open HomComplex

/-- The cochain complex of homomorphisms between two cochain complexes `F` and `G`.
In degree `n : ℤ`, it consists of the abelian group `HomComplex.Cochain F G n`. -/
@[simps! X d_hom_apply]
/-
**CochainComplex.HomComplex** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：HomComplex : CochainComplex AddCommGrpCat Int where X i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cochain complex of homomorphisms between two cochain complexes `F` and `G`.
In degree `n : ℤ`, it consists of the abelian group `HomComplex.Cochain F G n`.
-/
def HomComplex : CochainComplex AddCommGrpCat ℤ where
  X i := AddCommGrpCat.of (Cochain F G i)
  d i j := AddCommGrpCat.ofHom (δ_hom ℤ F G i j)
  shape _ _ hij := by ext; simp [δ_shape _ _ hij]
  d_comp_d' _ _ _ _ _ := by ext; simp [δ_δ]

namespace HomComplex

/-- The subgroup of cocycles in `Cochain F G n`. -/
/-
**CochainComplex.HomComplex.cocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Ho
mComplex`。
形式化陈述：cocycle : AddSubgroup (Cochain F G n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of cocycles in `Cochain F G n`.
-/
def cocycle : AddSubgroup (Cochain F G n) :=
  AddMonoidHom.ker (δ_hom ℤ F G n (n + 1)).toAddMonoidHom

/-- The type of `n`-cocycles, as a subtype of `Cochain F G n`. -/
/-
**CochainComplex.HomComplex.Cocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Ho
mComplex`。
形式化陈述：Cocycle : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `n`-cocycles, as a subtype of `Cochain F G n`.
-/
def Cocycle : Type v := cocycle F G n

namespace Cocycle

variable {F G}

/-
**CochainComplex.HomComplex.Cocycle.mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cocycle`。
形式化陈述：mem_iff (hnm : n + 1 = m) (z : Cochain F G n) : z in cocycle F G n ↔ δ n m
 z = 0
参数：hnm : n + 1 = m；z : Cochain F G n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_iff (hnm : n + 1 = m) (z : Cochain F G n) :
    z ∈ cocycle F G n ↔ δ n m z = 0 := by subst hnm; rfl

variable {n}
/-
**CochainComplex.HomComplex.Cocycle.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.H
omComplex.Cocycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Cocycle F G n) (Cochain F G n) where
  coe x := x.1

@[ext]
/-
**CochainComplex.HomComplex.Cocycle.ext** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.HomComplex.Cocycle`。
形式化陈述：ext {z₁ z₂ : Cocycle F G n} (h : (z₁ : Cochain F G n) = z₂) : z₁ = z₂
参数：h : (z₁ : Cochain F G n) = z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma ext {z₁ z₂ : Cocycle F G n} (h : (z₁ : Cochain F G n) = z₂) : z₁ = z₂ :=
  Subtype.ext h
/-
**CochainComplex.HomComplex.Cocycle.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.H
omComplex.Cocycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (Cocycle F G n) where
  smul r z := ⟨r • z.1, by
    have hz := z.2
    rw [mem_iff n (n + 1) rfl] at hz ⊢
    simp only [δ_smul, hz, smul_zero]⟩

variable (F G n)
/-
**CochainComplex.HomComplex.Cocycle.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.H
omComplex.Cocycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (Cocycle F G n) :=
  inferInstanceAs <| AddCommGroup (cocycle F G n)

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.coe_zero** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.HomComplex.Cocycle`。
形式化陈述：coe_zero : (↑(0 : Cocycle F G n) : Cochain F G n) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_zero : (↑(0 : Cocycle F G n) : Cochain F G n) = 0 := by rfl

variable {F G n}

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.coe_add** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cocycle`。
形式化陈述：coe_add (z₁ z₂ : Cocycle F G n) : (↑(z₁ + z₂) : Cochain F G n) = (z₁ : Coc
hain F G n) + (z₂ : Cochain F G n)
参数：z₁ z₂ : Cocycle F G n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_add (z₁ z₂ : Cocycle F G n) :
    (↑(z₁ + z₂) : Cochain F G n) = (z₁ : Cochain F G n) + (z₂ : Cochain F G n) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.coe_neg** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cocycle`。
形式化陈述：coe_neg (z : Cocycle F G n) : (↑(-z) : Cochain F G n) = -(z : Cochain F G 
n)
参数：z : Cocycle F G n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_neg (z : Cocycle F G n) :
    (↑(-z) : Cochain F G n) = -(z : Cochain F G n) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.HomComplex.Cocycle`。
形式化陈述：coe_smul (z : Cocycle F G n) (x : R) : (↑(x • z) : Cochain F G n) = x • (z
 : Cochain F G n)
参数：z : Cocycle F G n；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (z : Cocycle F G n) (x : R) :
    (↑(x • z) : Cochain F G n) = x • (z : Cochain F G n) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.coe_units_smul** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cocycle`。
形式化陈述：coe_units_smul (z : Cocycle F G n) (x : Rˣ) : (↑(x • z) : Cochain F G n) =
 x • (z : Cochain F G n)
参数：z : Cocycle F G n；x : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_units_smul (z : Cocycle F G n) (x : Rˣ) :
    (↑(x • z) : Cochain F G n) = x • (z : Cochain F G n) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.coe_sub** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cocycle`。
形式化陈述：coe_sub (z₁ z₂ : Cocycle F G n) : (↑(z₁ - z₂) : Cochain F G n) = (z₁ : Coc
hain F G n) - (z₂ : Cochain F G n)
参数：z₁ z₂ : Cocycle F G n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sub (z₁ z₂ : Cocycle F G n) :
    (↑(z₁ - z₂) : Cochain F G n) = (z₁ : Cochain F G n) - (z₂ : Cochain F G n) := rfl
/-
**CochainComplex.HomComplex.Cocycle.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.H
omComplex.Cocycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CochainComplex.HomComplex.Cocycle.mk** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex
.HomComplex.Cocycle`。
形式化陈述：mk (z : Cochain F G n) (m : Int) (hnm : n + 1 = m) (h : δ n m z = 0) : Coc
ycle F G n
参数：z : Cochain F G n；m : Int；hnm : n + 1 = m；h : δ n m z = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Cocycle F G n`, taking as inputs `z : Cochain F G n`, an intege
r
`m : ℤ` such that `n + 1 = m`, and the relation `δ n m z = 0`.
-/
def mk (z : Cochain F G n) (m : ℤ) (hnm : n + 1 = m) (h : δ n m z = 0) : Cocycle F G n :=
  ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cocycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq_zero {n : ℤ} (z : Cocycle F G n) (m : ℤ) : δ n m (z : Cochain F G n) = 0 := by
  by_cases h : n + 1 = m
  · rw [← mem_iff n m h]
    exact z.2
  · exact δ_shape n m h _

/-- The `0`-cocycle associated to a morphism in `CochainComplex C ℤ`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.HomComplex.Cocycle`。
形式化陈述：ofHom (φ : F ⟶ G) : Cocycle F G 0
参数：φ : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `0`-cocycle associated to a morphism in `CochainComplex C ℤ`.
-/
def ofHom (φ : F ⟶ G) : Cocycle F G 0 := mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

/-- The morphism in `CochainComplex C ℤ` associated to a `0`-cocycle. -/
@[simps]
/-
**CochainComplex.HomComplex.Cocycle.homOf** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.HomComplex.Cocycle`。
形式化陈述：homOf (z : Cocycle F G 0) : F ⟶ G where f i
参数：z : Cocycle F G 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in `CochainComplex C ℤ` associated to a `0`-cocycle.
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
/-
**CochainComplex.HomComplex.Cocycle.homOf_ofHom_eq_self** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：homOf_ofHom_eq_self (φ : F ⟶ G) : homOf (ofHom φ) = φ
参数：φ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homOf_ofHom_eq_self (φ : F ⟶ G) : homOf (ofHom φ) = φ := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.ofHom_homOf_eq_self** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：ofHom_homOf_eq_self (z : Cocycle F G 0) : ofHom (homOf z) = z
参数：z : Cocycle F G 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_homOf_eq_self (z : Cocycle F G 0) : ofHom (homOf z) = z := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe** 是 Mathlib 中的一个引
理，位于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：cochain_ofHom_homOf_eq_coe (z : Cocycle F G 0) : Cochain.ofHom (homOf z) =
 (z : Cochain F G 0)
参数：z : Cocycle F G 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cocycle.ofHom_homOf_eq_self`：ofHom_homOf_eq_se
lf (z : Cocycle F G 0) : ofHom (homOf z) = z
-/
lemma cochain_ofHom_homOf_eq_coe (z : Cocycle F G 0) :
    Cochain.ofHom (homOf z) = (z : Cochain F G 0) := by
  simpa only [Cocycle.ext_iff] using! ofHom_homOf_eq_self z

variable (F G)

/-- The additive equivalence between morphisms in `CochainComplex C ℤ` and `0`-cocycles. -/
@[simps]
/-
**CochainComplex.HomComplex.Cocycle.equivHom** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex.HomComplex.Cocycle`。
形式化陈述：equivHom : (F ⟶ G) ≃+ Cocycle F G 0 where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cocycle.homOf_ofHom_eq_self`：homOf_ofHom_eq_se
lf (φ : F ⟶ G) : homOf (ofHom φ) = φ
· 使用引理 `CochainComplex.HomComplex.Cocycle.ofHom_homOf_eq_self`：ofHom_homOf_eq_se
lf (z : Cocycle F G 0) : ofHom (homOf z) = z

--- 原说明 ---
The additive equivalence between morphisms in `CochainComplex C ℤ` and `0`-cocyc
les.
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
/-
**CochainComplex.HomComplex.Cocycle.diff** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.HomComplex.Cocycle`。
形式化陈述：diff : Cocycle K K 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `1`-cocycle given by the differential on a cochain complex.
-/
def diff : Cocycle K K 1 :=
  Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext p q hpq
    simp only [Cochain.zero_v, δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

variable (L n) in
/-- The inclusion `Cocycle K L n →+ Cochain K L n`. -/
@[simps]
/-
**CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom** 是 Mathlib 中的一个定义，位于命
名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：toCochainAddMonoidHom : Cocycle K L n ->+ Cochain K L n where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Cocycle K L n →+ Cochain K L n`.
-/
def toCochainAddMonoidHom : Cocycle K L n →+ Cochain K L n where
  toFun x := x
  map_zero' := by simp
  map_add' := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (L n) in
/-- `Cocycle K L n` is the kernel of the differential on `HomComplex K L`. -/
/-
**CochainComplex.HomComplex.Cocycle.isKernel** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex.HomComplex.Cocycle`。
形式化陈述：isKernel (hm : n + 1 = m) : IsLimit ((KernelFork.ofι (f
参数：hm : n + 1 = m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cocycle K L n` is the kernel of the differential on `HomComplex K L`.
-/
def isKernel (hm : n + 1 = m) :
    IsLimit ((KernelFork.ofι (f := (HomComplex K L).d n m)
      (AddCommGrpCat.ofHom (toCochainAddMonoidHom K L n))) (by cat_disch)) :=
  Fork.IsLimit.mk _
    (fun s ↦ AddCommGrpCat.ofHom
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
    (by cat_disch) (fun s l hl ↦ by ext : 3; simp [← hl])

end Cocycle

variable {F G}

@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_zero_cocycle {n : ℤ} (z₁ : Cochain F G n) (z₂ : Cocycle G K 0) (m : ℤ) :
    δ n m (z₁.comp z₂.1 (add_zero n)) =
      (δ n m z₁).comp z₂.1 (add_zero m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_ofHom {n : ℤ} (z₁ : Cochain F G n) (f : G ⟶ K) (m : ℤ) :
    δ n m (z₁.comp (Cochain.ofHom f) (add_zero n)) =
      (δ n m z₁).comp (Cochain.ofHom f) (add_zero m) := by
  rw [← Cocycle.ofHom_coe, δ_comp_zero_cocycle]


@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_cocycle_comp {n : ℤ} (z₁ : Cocycle F G 0) (z₂ : Cochain G K n) (m : ℤ) :
    δ n m (z₁.1.comp z₂ (zero_add n)) =
      z₁.1.comp (δ n m z₂) (zero_add m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_ofHom_comp {n : ℤ} (f : F ⟶ G) (z : Cochain G K n) (m : ℤ) :
    δ n m ((Cochain.ofHom f).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (δ n m z) (zero_add m) := by
  rw [← Cocycle.ofHom_coe, δ_zero_cocycle_comp]

/-- The precomposition of a cocycle with a morphism of cochain complexes. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.precomp** 是 Mathlib 中的一个定义，位于命名空间 `CochainCo
mplex.HomComplex.Cocycle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {F G K : CochainComplex C ℤ} →         {n
 : ℤ} → CochainComplex.HomComplex.Cocycle G K n → (F ⟶ G) → CochainComplex.HomCo
mplex.Cocycle F K n
参数：F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precomposition of a cocycle with a morphism of cochain complexes.
-/
def Cocycle.precomp {n : ℤ} (z : Cocycle G K n) (f : F ⟶ G) : Cocycle F K n :=
  Cocycle.mk ((Cochain.ofHom f).comp z (zero_add n)) _ rfl (by simp)

/-- The postcomposition of a cocycle with a morphism of cochain complexes. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex.HomComplex.Cocycle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {F G K : CochainComplex C ℤ} →         {n
 : ℤ} → CochainComplex.HomComplex.Cocycle F G n → (G ⟶ K) → CochainComplex.HomCo
mplex.Cocycle F K n
参数：G ⟶ K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The postcomposition of a cocycle with a morphism of cochain complexes.
-/
def Cocycle.postcomp {n : ℤ} (z : Cocycle F G n) (f : G ⟶ K) : Cocycle F K n :=
  Cocycle.mk (z.1.comp (Cochain.ofHom f) (add_zero n)) _ rfl (by simp)

namespace Cochain

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given two morphisms of complexes `φ₁ φ₂ : F ⟶ G`, the datum of a homotopy between `φ₁` and
`φ₂` is equivalent to the datum of a `1`-cochain `z` such that `δ (-1) 0 z` is the difference
of the zero cochains associated to `φ₂` and `φ₁`. -/
@[simps]
/-
**CochainComplex.HomComplex.Cochain.equivHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex.HomComplex.Cochain`。
形式化陈述：equivHomotopy (φ₁ φ₂ : F ⟶ G) : Homotopy φ₁ φ₂ ≃ { z : Cochain F G (-1) //
 Cochain.ofHom φ₁ = δ (-1) 0 z + Cochain.ofHom φ₂ } where toFun ho
参数：φ₁ φ₂ : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two morphisms of complexes `φ₁ φ₂ : F ⟶ G`, the datum of a homotopy betwee
n `φ₁` and
`φ₂` is equivalent to the datum of a `1`-cochain `z` such that `δ (-1) 0 z` is t
he difference
of the zero cochains associated to `φ₂` and `φ₁`.
-/
def equivHomotopy (φ₁ φ₂ : F ⟶ G) :
    Homotopy φ₁ φ₂ ≃
      { z : Cochain F G (-1) // Cochain.ofHom φ₁ = δ (-1) 0 z + Cochain.ofHom φ₂ } where
  toFun ho := ⟨Cochain.ofHomotopy ho, by simp only [δ_ofHomotopy, sub_add_cancel]⟩
  invFun z :=
    { hom := fun i j => if hij : i + (-1) = j then z.1.v i j hij else 0
      zero := fun i j (hij : j + 1 ≠ i) => dif_neg (fun _ => hij (by lia))
      comm := fun p => by
        have eq := Cochain.congr_v z.2 p p (add_zero p)
        have h₁ : (ComplexShape.up ℤ).Rel (p - 1) p := by simp
        have h₂ : (ComplexShape.up ℤ).Rel p (p + 1) := by simp
        simp only [δ_neg_one_cochain, Cochain.ofHom_v, ComplexShape.up_Rel, Cochain.add_v,
          Homotopy.nullHomotopicMap'_f h₁ h₂] at eq
        rw [dNext_eq _ h₂, prevD_eq _ h₁, eq, dif_pos, dif_pos] }
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
/-
**CochainComplex.HomComplex.Cochain.equivHomotopy_apply_of_eq** 是 Mathlib 中的一个引理
，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：equivHomotopy_apply_of_eq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) : (equivHomotopy _
 _ (Homotopy.ofEq h)).1 = 0
参数：h : φ₁ = φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma equivHomotopy_apply_of_eq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    (equivHomotopy _ _ (Homotopy.ofEq h)).1 = 0 := rfl
/-
**CochainComplex.HomComplex.Cochain.ofHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：ofHom_injective {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂) : f₁ = f₂
参数：h : ofHom f₁ = ofHom f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
-/
lemma ofHom_injective {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂) : f₁ = f₂ :=
  (Cocycle.equivHom F G).injective (by ext1; exact h)

/-- The cochain in `Cochain K L n` that is given by a single
morphism `K.X p ⟶ L.X q` and is zero otherwise. (As we do not check
that `p + n = q`, this will be the zero cochain when `p + n ≠ q`.) -/
/-
**CochainComplex.HomComplex.Cochain.single** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：single {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) : Cochain K L n
参数：f : K.X p ⟶ L.X q；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cochain in `Cochain K L n` that is given by a single
morphism `K.X p ⟶ L.X q` and is zero otherwise. (As we do not check
that `p + n = q`, this will be the zero cochain when `p + n ≠ q`.)
-/
def single {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) :
    Cochain K L n :=
  Cochain.mk (fun p' q' _ =>
    if h : p = p' ∧ q = q'
      then (K.XIsoOfEq h.1).inv ≫ f ≫ (L.XIsoOfEq h.2).hom
      else 0)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.single_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：single_v {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (hpq : p + n = q) : (si
ngle f n).v p q hpq = f
参数：f : K.X p ⟶ L.X q；n : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma single_v {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (hpq : p + n = q) :
    (single f n).v p q hpq = f := by
  dsimp [single]
  rw [if_pos, id_comp, comp_id]
  tauto
/-
**CochainComplex.HomComplex.Cochain.single_v_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：single_v_eq_zero {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (
hpq' : p' + n = q') (hp' : p' != p) : (single f n).v p' q' hpq' = 0
参数：f : K.X p ⟶ L.X q；n : Int；p' q' : Int；hpq' : p' + n = q'；hp' : p' != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma single_v_eq_zero {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hp' : p' ≠ p) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hp' (by lia)

/-- Variant of `single_v_eq_zero` where the assumption is `q' ≠ q` rather than `p' ≠ p`. -/
/-
**CochainComplex.HomComplex.Cochain.single_v_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.HomComplex.Cochain`。
形式化陈述：single_v_eq_zero' {p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) 
(hpq' : p' + n = q') (hq' : q' != q) : (single f n).v p' q' hpq' = 0
参数：f : K.X p ⟶ L.X q；n : Int；p' q' : Int；hpq' : p' + n = q'；hq' : q' != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
Variant of `single_v_eq_zero` where the assumption is `q' ≠ q` rather than `p' ≠
 p`.
-/
lemma single_v_eq_zero' {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hq' : q' ≠ q) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  grind

variable (K L) in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.single_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.HomComplex.Cochain`。
形式化陈述：single_zero (p q n : Int) : (single (p
参数：p q n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v`：single_v {p q : Int} (f : K.
X p ⟶ L.X q) (n : Int) (hpq : p + n = q) : (single f n).v p q hpq = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v_eq_zero'`：single_v_eq_zero' {
p q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q') (hq'
 : q' != q) : (single f n).v p' q' hpq' =…
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v_eq_zero`：single_v_eq_zero {p 
q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q') (hp' :
 p' != p) : (single f n).v p' q' hpq' = …
-/
lemma single_zero (p q n : ℤ) :
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
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_single {p q : ℤ} (f : K.X p ⟶ L.X q) (n m : ℤ) (hm : n + 1 = m)
    (p' q' : ℤ) (hp' : p' + 1 = p) (hq' : q + 1 = q') :
    δ n m (single f n) = single (f ≫ L.d q q') m + m.negOnePow • single (K.d p' p ≫ f) m := by
  ext p'' q'' hpq''
  rw [δ_v n m hm (single f n) p'' q'' (by lia) (q'' - 1) (p'' + 1) rfl (by lia),
    add_v, units_smul_v]
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

/-- If `Φ : C ⥤ D` is an additive functor, a cochain `z : Cochain K L n` between
cochain complexes in `C` can be mapped to a cochain between the cochain complexes
in `D` obtained by applying the functor
`Φ.mapHomologicalComplex _ : CochainComplex C ℤ ⥤ CochainComplex D ℤ`. -/
/-
**CochainComplex.HomComplex.Cochain.map** 是 Mathlib 中的一个定义，位于命名空间 `CochainComple
x.HomComplex.Cochain`。
形式化陈述：map : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComple
x _).obj L) n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If `Φ : C ⥤ D` is an additive functor, a cochain `z : Cochain K L n` between
cochain complexes in `C` can be mapped to a cochain between the cochain complexe
s
in `D` obtained by applying the functor
`Φ.mapHomologicalComplex _ : CochainComplex C ℤ ⥤ CochainComplex D ℤ`.
-/
def map : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cochain.mk (fun p q hpq => Φ.map (z.v p q hpq))

@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.HomComplex.Cochain`。
形式化陈述：map_v (p q : Int) (hpq : p + n = q) : (z.map Φ).v p q hpq = Φ.map (z.v p q
 hpq)
参数：p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma map_v (p q : ℤ) (hpq : p + n = q) : (z.map Φ).v p q hpq = Φ.map (z.v p q hpq) := rfl

@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_add** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {K L : CochainComplex C ℤ} {n : ℤ} {D : Type u_2} [inst
_2 : CategoryTheory.Category.{v_1, u_2} D]   [inst_3 : CategoryTheory.Preadditiv
e D] (z z' : CochainComplex.HomComplex.Cochain K L n)   (Φ : CategoryTheory.Func
tor C D) [inst_4 : Φ.Additive], (z + z').map Φ = z.map Φ + z'.map Φ
参数：z z' : CochainComplex.HomComplex.Cochain K L n；Φ : CategoryTheory.Functor C D
；z + z'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
protected lemma map_add : (z + z').map Φ = z.map Φ + z'.map Φ := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {K L : CochainComplex C ℤ} {n : ℤ} {D : Type u_2} [inst
_2 : CategoryTheory.Category.{v_1, u_2} D]   [inst_3 : CategoryTheory.Preadditiv
e D] (z : CochainComplex.HomComplex.Cochain K L n) (Φ : CategoryTheory.Functor C
 D)   [inst_4 : Φ.Additive], (-z).map Φ = -z.map Φ
参数：z : CochainComplex.HomComplex.Cochain K L n；Φ : CategoryTheory.Functor C D；-z
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_neg`：map_neg {X Y : C} {f : X ⟶ Y} : F.map (-
f) = -F.map f
-/
protected lemma map_neg : (-z).map Φ = -z.map Φ := by cat_disch

@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   {K L : CochainComplex C ℤ} {n : ℤ} {D : Type u_2} [inst
_2 : CategoryTheory.Category.{v_1, u_2} D]   [inst_3 : CategoryTheory.Preadditiv
e D] (z z' : CochainComplex.HomComplex.Cochain K L n)   (Φ : CategoryTheory.Func
tor C D) [inst_4 : Φ.Additive], (z - z').map Φ = z.map Φ - z'.map Φ
参数：z z' : CochainComplex.HomComplex.Cochain K L n；Φ : CategoryTheory.Functor C D
；z - z'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_sub`：map_sub {X Y : C} {f g : X ⟶ Y} : F.map 
(f - g) = F.map f - F.map g
-/
protected lemma map_sub : (z - z').map Φ = z.map Φ - z'.map Φ := by cat_disch

variable (K L n)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   (K L : CochainComplex C ℤ) (n : ℤ) {D : Type u_2} [inst
_2 : CategoryTheory.Category.{v_1, u_2} D]   [inst_3 : CategoryTheory.Preadditiv
e D] (Φ : CategoryTheory.Functor C D) [inst_4 : Φ.Additive],   CochainComplex.Ho
mComplex.Cochain.map 0 Φ = 0
参数：K L : CochainComplex C ℤ；n : ℤ；Φ : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
protected lemma map_zero : (0 : Cochain K L n).map Φ = 0 := by cat_disch

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：map_comp {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h 
: n₁ + n₂ = n₁₂) (Φ : C ⥤ D) [Φ.Additive] : (Cochain.comp z₁ z₂ h).map Φ = Cocha
in.comp (z₁.map Φ) (z₂.map Φ) h
参数：z₁ : Cochain F G n₁；z₂ : Cochain G K n₂；h : n₁ + n₂ = n₁₂；Φ : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (Φ : C ⥤ D) [Φ.Additive] :
    (Cochain.comp z₁ z₂ h).map Φ = Cochain.comp (z₁.map Φ) (z₂.map Φ) h := by
  ext p q hpq
  dsimp
  simp only [map_v, comp_v _ _ h p _ q rfl (by lia), Φ.map_comp]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.map_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：map_ofHom : (Cochain.ofHom f).map Φ = Cochain.ofHom ((Φ.mapHomologicalComp
lex _).map f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.mapHomologicalComplex_map_f`：∀ {ι : Type u_1} {W₁
 : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁]   [i
nst_1 : CategoryTheory.Category.{v_3, u_…
-/
lemma map_ofHom :
    (Cochain.ofHom f).map Φ = Cochain.ofHom ((Φ.mapHomologicalComplex _).map f) := by cat_disch

end Cochain

variable (n)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

