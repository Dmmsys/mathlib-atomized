/-
Copyright (c) 2024 María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# Skew Monoid Algebras

Given a monoid `G` acting on a ring `k`, the skew monoid algebra of `G` over `k` is the set
of finitely supported functions `f : G → k` for which addition is defined pointwise and
multiplication of two elements `f` and `g` is given by the finitely supported function whose
value at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y = a`,
where `•` denotes the action of `G` on `k`. When this action is trivial, this product is
the usual convolution product.

In fact the construction of the skew monoid algebra makes sense when `G` is not even a monoid, but
merely a magma, i.e., when `G` carries a multiplication which is not required to satisfy any
conditions at all, and `k` is a not-necessarily-associative semiring. In this case the construction
yields a not-necessarily-unital, not-necessarily-associative algebra.

## Main Definitions
- `SkewMonoidAlgebra k G`: the skew monoid algebra of `G` over `k` is the type of finite formal
  `k`-linear combinations of terms of `G`, endowed with a skewed convolution product.

-/

@[expose] public section


noncomputable section

/--
Definition of `SkewMonoidAlgebra` / `SkewMonoidAlgebra` 的定义

English:
structure SkewMonoidAlgebra
  parameters: (k : Type*) (G : Type*) [Zero k]
  axioms and operations (2):
    - ofCoeff : :
    - coeff : G ->₀ k

中文:
结构 斜幺半群代数
  参数: (k : 类型) (G : 类型) [零 k]
  公理与运算 (2 个):
    - ofCoeff : :
    - coeff : G ->₀ k
-/
structure SkewMonoidAlgebra (k : Type*) (G : Type*) [Zero k] where
  /-- The natural map from `G →₀ k` to `SkewMonoidAlgebra k G`. -/
  ofCoeff ::
  /-- The natural map from `SkewMonoidAlgebra k G` to `G →₀ k`. -/
  coeff : G ->₀ k

open Function
namespace SkewMonoidAlgebra

initialize_simps_projections SkewMonoidAlgebra (as_prefix coeff)

@[deprecated (since := "2026-07-06"), reducible] alias ofFinsupp := ofCoeff
@[deprecated (since := "2026-07-06"), reducible] alias toFinsupp := coeff

variable {k G : Type*}

section AddMonoid

variable [AddMonoid k]

/--
lemma `eta` / 引理 `eta`

English:
lemma eta
  given: (f : SkewMonoidAlgebra k G)
  statement: ofCoeff f.coeff = f
  proof: rfl

中文:
引理 eta
  条件: (f : 斜幺半群代数 k G)
  结论: ofCoeff f.coeff = f
  证明: rfl
-/
@[simp] lemma eta (f : SkewMonoidAlgebra k G) : ofCoeff f.coeff = f := rfl
/--
lemma `coeff_ofCoeff` / 引理 `coeff_ofCoeff`

English:
lemma coeff_ofCoeff
  given: (f : G ->₀ k)
  statement: coeff (ofCoeff f) = f
  proof: rfl

中文:
引理 coeff_ofCoeff
  条件: (f : G ->₀ k)
  结论: coeff (ofCoeff f) = f
  证明: rfl
-/
@[simp] lemma coeff_ofCoeff (f : G ->₀ k) : coeff (ofCoeff f) = f := rfl

set_option backward.privateInPublic true in
@[irreducible]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: :

中文:
定义 add
  签名: :
-/
private def add :
    SkewMonoidAlgebra k G -> SkewMonoidAlgebra k G -> SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: {S : Type*} [SMulZeroClass S k]

中文:
定义 smul
  签名: {S : 类型} [SMulZero类 S k]
-/
private def smul {S : Type*} [SMulZeroClass S k] :
    S -> SkewMonoidAlgebra k G -> SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (SkewMonoidAlgebra k G)
  body: ⟨⟨0⟩⟩

中文:
实例 :
  签名: 零 (斜幺半群代数 k G)
  定义体: ⟨⟨0⟩⟩
-/
instance : Zero (SkewMonoidAlgebra k G) := ⟨⟨0⟩⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (SkewMonoidAlgebra k G)
  body: ⟨add⟩

中文:
实例 :
  签名: 加法 (斜幺半群代数 k G)
  定义体: ⟨add⟩
-/
instance : Add (SkewMonoidAlgebra k G) := ⟨add⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance {S : Type*} [SMulZeroClass S k] :
    SMulZeroClass S (SkewMonoidAlgebra k G) where
  smul s f := smul s f
  smul_zero a := by exact congr_arg ofCoeff (smul_zero a)

@[simp]
/--
theorem `ofCoeff_zero` / 定理 `ofCoeff_zero`

English:
theorem ofCoeff_zero
  statement: (⟨0⟩ : SkewMonoidAlgebra k G) = 0
  proof: rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_zero := ofCoeff_zero

@[simp]

中文:
定理 ofCoeff_zero
  结论: (⟨0⟩ : 斜幺半群代数 k G) = 0
  证明: rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_zero := ofCoeff_zero

@[simp]
-/
theorem ofCoeff_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0 := rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_zero := ofCoeff_zero

@[simp]
/--
theorem `ofCoeff_add` / 定理 `ofCoeff_add`

English:
theorem ofCoeff_add
  given: {a b}
  statement: (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩
  proof: show _ = add _ _ by rw [add]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_add := ofCoeff_add

@[simp]

中文:
定理 ofCoeff_add
  条件: {a b}
  结论: (⟨a + b⟩ : 斜幺半群代数 k G) = ⟨a⟩ + ⟨b⟩
  证明: show _ = add _ _ by rw [add]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_add := ofCoeff_add

@[simp]
-/
theorem ofCoeff_add {a b} : (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_add := ofCoeff_add

@[simp]
/--
theorem `ofCoeff_smul` / 定理 `ofCoeff_smul`

English:
theorem ofCoeff_smul
  given: {S : Type*} [SMulZeroClass S k] (a : S) (b : G ->₀ k)
  proof: show _ = smul _ _ by rw [smul]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_smul := ofCoeff_smul

@[simp]

中文:
定理 ofCoeff_smul
  条件: {S : 类型} [SMulZero类 S k] (a : S) (b : G ->₀ k)
  证明: show _ = smul _ _ by rw [smul]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_smul := ofCoeff_smul

@[simp]
-/
theorem ofCoeff_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G ->₀ k) :
    (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G) :=
  show _ = smul _ _ by rw [smul]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_smul := ofCoeff_smul

@[simp]
/--
theorem `coeff_zero` / 定理 `coeff_zero`

English:
theorem coeff_zero
  statement: (0 : SkewMonoidAlgebra k G).coeff = 0
  proof: rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_zero := coeff_zero

@[simp]

中文:
定理 coeff_zero
  结论: (0 : 斜幺半群代数 k G).coeff = 0
  证明: rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_zero := coeff_zero

@[simp]
-/
theorem coeff_zero : (0 : SkewMonoidAlgebra k G).coeff = 0 := rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_zero := coeff_zero

@[simp]
/--
theorem `coeff_add` / 定理 `coeff_add`

English:
theorem coeff_add
  given: (a b : SkewMonoidAlgebra k G)
  proof: by
  rw [← ofCoeff_add]

@[deprecated (since := "2026-07-04")] alias toFinsupp_add := coeff_add

@[simp]

中文:
定理 coeff_add
  条件: (a b : 斜幺半群代数 k G)
  证明: by
  rw [← ofCoeff_add]

@[deprecated (since := "2026-07-04")] alias toFinsupp_add := coeff_add

@[simp]

Depends on / 依赖: ofCoeff_add
-/
theorem coeff_add (a b : SkewMonoidAlgebra k G) :
    (a + b).coeff = a.coeff + b.coeff := by
  rw [← ofCoeff_add]

@[deprecated (since := "2026-07-04")] alias toFinsupp_add := coeff_add

@[simp]
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra k G)
  proof: by
  rw [← ofCoeff_smul]

@[deprecated (since := "2026-07-04")] alias toFinsupp_smul := coeff_smul

中文:
定理 coeff_smul
  条件: {S : 类型} [SMulZero类 S k] (a : S) (b : 斜幺半群代数 k G)
  证明: by
  rw [← ofCoeff_smul]

@[deprecated (since := "2026-07-04")] alias toFinsupp_smul := coeff_smul

Depends on / 依赖: ofCoeff_smul
-/
theorem coeff_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra k G) :
    (a • b).coeff = a • b.coeff := by
  rw [← ofCoeff_smul]

@[deprecated (since := "2026-07-04")] alias toFinsupp_smul := coeff_smul

/--
theorem `_root_.IsSMulRegular.skewMonoidAlgebra` / 定理 `_root_.IsSMulRegular.skewMonoidAlgebra`

English:
theorem _root_.IsSMulRegular.skewMonoidAlgebra
  statement: {S : Type*} [Monoid S] [DistribMulAction S k] {a : S}

中文:
定理 _root_.IsSMulRegular.skewMonoidAlgebra
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S k] {a : S}
-/
theorem _root_.IsSMulRegular.skewMonoidAlgebra {S : Type*} [Monoid S] [DistribMulAction S k] {a : S}
    (ha : IsSMulRegular k a) : IsSMulRegular (SkewMonoidAlgebra k G) a
  | ⟨_⟩, ⟨_⟩, h => by
exact congr_arg _ ha.finsupp (ofCoeff.inj h)

/--
theorem `coeff_injective` / 定理 `coeff_injective`

English:
theorem coeff_injective
  proof: fun ⟨_⟩ _ => congr_arg _

@[deprecated (since := "2026-07-04")] alias toFinsupp_injective := coeff_injective

@[simp]

中文:
定理 coeff_injective
  证明: fun ⟨_⟩ _ => congr_arg _

@[deprecated (since := "2026-07-04")] alias toFinsupp_injective := coeff_injective

@[simp]

Depends on / 依赖: congr_arg
-/
theorem coeff_injective :
    Function.Injective (coeff : SkewMonoidAlgebra k G -> Finsupp _ _) :=
  fun ⟨_⟩ _ => congr_arg _

@[deprecated (since := "2026-07-04")] alias toFinsupp_injective := coeff_injective

@[simp]
/--
theorem `coeff_inj` / 定理 `coeff_inj`

English:
theorem coeff_inj
  given: {a b : SkewMonoidAlgebra k G}
  statement: a.coeff = b.coeff ↔ a = b
  proof: coeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias toFinsupp_inj := coeff_inj

中文:
定理 coeff_inj
  条件: {a b : 斜幺半群代数 k G}
  结论: a.coeff = b.coeff ↔ a = b
  证明: coeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias toFinsupp_inj := coeff_inj

Depends on / 依赖: coeff_injective, coeff_injective.eq_iff, eq_iff
-/
theorem coeff_inj {a b : SkewMonoidAlgebra k G} : a.coeff = b.coeff ↔ a = b :=
  coeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias toFinsupp_inj := coeff_inj

/--
theorem `ofCoeff_injective` / 定理 `ofCoeff_injective`

English:
theorem ofCoeff_injective
  proof: fun _ _ => congr_arg coeff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_injective := ofCoeff_injective

中文:
定理 ofCoeff_injective
  证明: fun _ _ => congr_arg coeff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_injective := ofCoeff_injective

Depends on / 依赖: congr_arg
-/
theorem ofCoeff_injective :
    Function.Injective (ofCoeff : Finsupp _ _ -> SkewMonoidAlgebra k G) :=
  fun _ _ => congr_arg coeff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_injective := ofCoeff_injective

/--
theorem `ofCoeff_inj` / 定理 `ofCoeff_inj`

English:
theorem ofCoeff_inj
  given: {a b}
  statement: (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b
  proof: ofCoeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_inj := ofCoeff_inj

@[simp]

中文:
定理 ofCoeff_inj
  条件: {a b}
  结论: (⟨a⟩ : 斜幺半群代数 k G) = ⟨b⟩ ↔ a = b
  证明: ofCoeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_inj := ofCoeff_inj

@[simp]

Depends on / 依赖: eq_iff, ofCoeff_injective, ofCoeff_injective.eq_iff
-/
theorem ofCoeff_inj {a b} : (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b :=
  ofCoeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_inj := ofCoeff_inj

@[simp]
/--
theorem `coeff_eq_zero` / 定理 `coeff_eq_zero`

English:
theorem coeff_eq_zero
  given: {a : SkewMonoidAlgebra k G}
  statement: a.coeff = 0 ↔ a = 0
  proof: coeff_inj

@[deprecated (since := "2026-07-04")] alias toFinsupp_eq_zero := coeff_eq_zero

@[simp]

中文:
定理 coeff_eq_zero
  条件: {a : 斜幺半群代数 k G}
  结论: a.coeff = 0 ↔ a = 0
  证明: coeff_inj

@[deprecated (since := "2026-07-04")] alias toFinsupp_eq_zero := coeff_eq_zero

@[simp]

Depends on / 依赖: coeff_inj
-/
theorem coeff_eq_zero {a : SkewMonoidAlgebra k G} : a.coeff = 0 ↔ a = 0 :=
  coeff_inj

@[deprecated (since := "2026-07-04")] alias toFinsupp_eq_zero := coeff_eq_zero

@[simp]
/--
theorem `ofCoeff_eq_zero` / 定理 `ofCoeff_eq_zero`

English:
theorem ofCoeff_eq_zero
  given: {a}
  statement: (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0
  proof: ofCoeff_inj

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_zero := ofCoeff_eq_zero

中文:
定理 ofCoeff_eq_zero
  条件: {a}
  结论: (⟨a⟩ : 斜幺半群代数 k G) = 0 ↔ a = 0
  证明: ofCoeff_inj

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_zero := ofCoeff_eq_zero

Depends on / 依赖: ofCoeff_inj
-/
theorem ofCoeff_eq_zero {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0 :=
  ofCoeff_inj

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_zero := ofCoeff_eq_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SkewMonoidAlgebra k G)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (斜幺半群代数 k G)
  定义体: ⟨0⟩
-/
instance : Inhabited (SkewMonoidAlgebra k G) := ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: k] [Nonempty G] :
  body: Function.Injective.nontrivial ofCoeff_injective

中文:
实例 [非平凡
  签名: k] [非空 G] :
  定义体: Function.Injective.nontrivial ofCoeff_injective

Depends on / 依赖: Function, Function.Injective.nontrivial, Injective, nontrivial, ofCoeff_injective
-/
instance [Nontrivial k] [Nonempty G] :
    Nontrivial (SkewMonoidAlgebra k G) := Function.Injective.nontrivial ofCoeff_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: k] : Unique (SkewMonoidAlgebra k G)
  body: Function.Injective.unique coeff_injective

中文:
实例 [子单例
  签名: k] : 唯一 (斜幺半群代数 k G)
  定义体: Function.Injective.unique coeff_injective

Depends on / 依赖: Function, Function.Injective.unique, Injective, coeff_injective, unique
-/
instance [Subsingleton k] : Unique (SkewMonoidAlgebra k G) :=
  Function.Injective.unique coeff_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (SkewMonoidAlgebra k G)
  body: coeff_injective.addMonoid _ coeff_zero coeff_add
    (fun _ _ => coeff_smul _ _)

中文:
实例 :
  签名: 加法幺半群 (斜幺半群代数 k G)
  定义体: coeff_injective.addMonoid _ coeff_zero coeff_add
    (fun _ _ => coeff_smul _ _)

Depends on / 依赖: addMonoid, coeff_add, coeff_injective, coeff_injective.addMonoid, coeff_zero
-/
instance : AddMonoid (SkewMonoidAlgebra k G) where
  __ := coeff_injective.addMonoid _ coeff_zero coeff_add
    (fun _ _ => coeff_smul _ _)

section Support

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (p : SkewMonoidAlgebra k G)
  body: p.coeff.support

@[simp]

中文:
定义 support
  签名: (p : 斜幺半群代数 k G)
  定义体: p.coeff.support

@[simp]

Depends on / 依赖: p.coeff.support, support
-/
def support (p : SkewMonoidAlgebra k G) : Finset G := p.coeff.support

@[simp]
/--
theorem `support_ofCoeff` / 定理 `support_ofCoeff`

English:
theorem support_ofCoeff
  given: (p)
  statement: support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support
  proof: by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_ofFinsupp := support_ofCoeff

中文:
定理 support_ofCoeff
  条件: (p)
  结论: support (⟨p⟩ : 斜幺半群代数 k G) = p.support
  证明: by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_ofFinsupp := support_ofCoeff

Depends on / 依赖: support
-/
theorem support_ofCoeff (p) : support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support := by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_ofFinsupp := support_ofCoeff

/--
theorem `support_coeff` / 定理 `support_coeff`

English:
theorem support_coeff
  given: (p : SkewMonoidAlgebra k G)
  statement: p.coeff.support = p.support
  proof: by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_toFinsupp := support_coeff

@[simp]

中文:
定理 support_coeff
  条件: (p : 斜幺半群代数 k G)
  结论: p.coeff.support = p.support
  证明: by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_toFinsupp := support_coeff

@[simp]

Depends on / 依赖: support
-/
theorem support_coeff (p : SkewMonoidAlgebra k G) : p.coeff.support = p.support := by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_toFinsupp := support_coeff

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: (0 : SkewMonoidAlgebra k G).support = ∅
  proof: rfl

@[simp]

中文:
定理 support_zero
  结论: (0 : 斜幺半群代数 k G).support = ∅
  证明: rfl

@[simp]
-/
theorem support_zero : (0 : SkewMonoidAlgebra k G).support = ∅ := rfl

@[simp]
/--
theorem `support_eq_empty` / 定理 `support_eq_empty`

English:
theorem support_eq_empty
  given: {p}
  statement: p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0
  proof: by
  rcases p
  simp only [support, Finsupp.support_eq_empty, ofCoeff_eq_zero]

中文:
定理 support_eq_empty
  条件: {p}
  结论: p.support = ∅ ↔ (p : 斜幺半群代数 k G) = 0
  证明: by
  rcases p
  simp only [support, Finsupp.support_eq_empty, ofCoeff_eq_zero]

Depends on / 依赖: Finsupp, Finsupp.support_eq_empty, ofCoeff_eq_zero, support, support_eq_empty
-/
theorem support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0 := by
  rcases p
  simp only [support, Finsupp.support_eq_empty, ofCoeff_eq_zero]

/--
lemma `support_add` / 引理 `support_add`

English:
lemma support_add
  given: [DecidableEq G] {p q : SkewMonoidAlgebra k G}
  proof: by
  simpa [support] using Finsupp.support_add

中文:
引理 support_add
  条件: [DecidableEq G] {p q : 斜幺半群代数 k G}
  证明: by
  simpa [support] using Finsupp.support_add

Depends on / 依赖: Finsupp, Finsupp.support_add, support, support_add
-/
lemma support_add [DecidableEq G] {p q : SkewMonoidAlgebra k G} :
    (p + q).support subseteq p.support union q.support := by
  simpa [support] using Finsupp.support_add

end Support

section Coeff

@[deprecated (since := "2026-07-06")] alias coeff_ofFinsupp := coeff_ofCoeff

@[deprecated "Now a syntactic tautology" (since := "2026-07-04"), nolint synTaut]
/--
theorem `toFinsupp_apply` / 定理 `toFinsupp_apply`

English:
theorem toFinsupp_apply
  given: (f : SkewMonoidAlgebra k G) (g)
  statement: f.coeff g = f.coeff g
  proof: rfl

@[simp]

中文:
定理 toFinsupp_apply
  条件: (f : 斜幺半群代数 k G) (g)
  结论: f.coeff g = f.coeff g
  证明: rfl

@[simp]
-/
theorem toFinsupp_apply (f : SkewMonoidAlgebra k G) (g) : f.coeff g = f.coeff g := rfl

@[simp]
/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: {f : SkewMonoidAlgebra k G} {a : G}
  statement: a in f.support ↔ f.coeff a != 0
  proof: by
  rcases f with ⟨⟩
  simp only [support_ofCoeff, Finsupp.mem_support_iff, ne_eq]

中文:
定理 mem_support_iff
  条件: {f : 斜幺半群代数 k G} {a : G}
  结论: a in f.support ↔ f.coeff a != 0
  证明: by
  rcases f with ⟨⟩
  simp only [support_ofCoeff, Finsupp.mem_support_iff, ne_eq]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, mem_support_iff, ne_eq, support_ofCoeff
-/
theorem mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a in f.support ↔ f.coeff a != 0 := by
  rcases f with ⟨⟩
  simp only [support_ofCoeff, Finsupp.mem_support_iff, ne_eq]

/--
theorem `notMem_support_iff` / 定理 `notMem_support_iff`

English:
theorem notMem_support_iff
  given: {f : SkewMonoidAlgebra k G} {a : G}
  proof: by
  simp only [mem_support_iff, ne_eq, not_not]

中文:
定理 notMem_support_iff
  条件: {f : 斜幺半群代数 k G} {a : G}
  证明: by
  simp only [mem_support_iff, ne_eq, not_not]

Depends on / 依赖: mem_support_iff, ne_eq, not_not
-/
theorem notMem_support_iff {f : SkewMonoidAlgebra k G} {a : G} :
    a ∉ f.support ↔ f.coeff a = 0 := by
  simp only [mem_support_iff, ne_eq, not_not]

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {p q : SkewMonoidAlgebra k G}
  statement: p = q ↔ forall n, coeff p n = coeff q n
  proof: by
  rcases p with ⟨f : G ->₀ k⟩
  rcases q with ⟨g : G ->₀ k⟩
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]

中文:
定理 ext_iff
  条件: {p q : 斜幺半群代数 k G}
  结论: p = q ↔ 对任意 n, coeff p n = coeff q n
  证明: by
  rcases p with ⟨f : G ->₀ k⟩
  rcases q with ⟨g : G ->₀ k⟩
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
theorem ext_iff {p q : SkewMonoidAlgebra k G} : p = q ↔ forall n, coeff p n = coeff q n := by
  rcases p with ⟨f : G ->₀ k⟩
  rcases q with ⟨g : G ->₀ k⟩
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : SkewMonoidAlgebra k G}
  statement: (forall a, coeff p a = coeff q a) -> p = q
  proof: ext_iff.2

中文:
定理 ext
  条件: {p q : 斜幺半群代数 k G}
  结论: (对任意 a, coeff p a = coeff q a) -> p = q
  证明: ext_iff.2

Depends on / 依赖: ext_iff
-/
theorem ext {p q : SkewMonoidAlgebra k G} : (forall a, coeff p a = coeff q a) -> p = q := ext_iff.2

end Coeff

section Single

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (a : G) (b : k)
  body: ⟨Finsupp.single a b⟩

@[simp]

中文:
定义 single
  签名: (a : G) (b : k)
  定义体: ⟨Finsupp.single a b⟩

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
def single (a : G) (b : k) : SkewMonoidAlgebra k G := ⟨Finsupp.single a b⟩

@[simp]
/--
theorem `coeff_single` / 定理 `coeff_single`

English:
theorem coeff_single
  given: (a : G) (b : k)
  statement: (single a b).coeff = Finsupp.single a b
  proof: rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_single := coeff_single

@[simp]

中文:
定理 coeff_single
  条件: (a : G) (b : k)
  结论: (single a b).coeff = 有限支撑.single a b
  证明: rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_single := coeff_single

@[simp]
-/
theorem coeff_single (a : G) (b : k) : (single a b).coeff = Finsupp.single a b := rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_single := coeff_single

@[simp]
/--
theorem `ofCoeff_single` / 定理 `ofCoeff_single`

English:
theorem ofCoeff_single
  given: (a : G) (b : k)
  statement: ⟨Finsupp.single a b⟩ = single a b
  proof: rfl

@[deprecated (since := "2026-07-06")] alias ofFinsupp_single := ofCoeff_single

中文:
定理 ofCoeff_single
  条件: (a : G) (b : k)
  结论: ⟨有限支撑.single a b⟩ = single a b
  证明: rfl

@[deprecated (since := "2026-07-06")] alias ofFinsupp_single := ofCoeff_single
-/
theorem ofCoeff_single (a : G) (b : k) : ⟨Finsupp.single a b⟩ = single a b := rfl

@[deprecated (since := "2026-07-06")] alias ofFinsupp_single := ofCoeff_single

/--
theorem `coeff_single_apply` / 定理 `coeff_single_apply`

English:
theorem coeff_single_apply
  given: {a a' : G} {b : k} [Decidable (a = a')]
  proof: by
  simp [Finsupp.single_apply]

中文:
定理 coeff_single_apply
  条件: {a a' : G} {b : k} [可判定 (a = a')]
  证明: by
  simp [Finsupp.single_apply]

Depends on / 依赖: Finsupp, Finsupp.single_apply, single_apply
-/
theorem coeff_single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    coeff (single a b) a' = if a = a' then b else 0 := by
  simp [Finsupp.single_apply]

/--
theorem `single_zero_right` / 定理 `single_zero_right`

English:
theorem single_zero_right
  given: (a : G)
  statement: single a (0 : k) = 0
  proof: by
  simp [← coeff_inj]

@[simp]

中文:
定理 single_zero_right
  条件: (a : G)
  结论: single a (0 : k) = 0
  证明: by
  simp [← coeff_inj]

@[simp]

Depends on / 依赖: coeff_inj
-/
theorem single_zero_right (a : G) : single a (0 : k) = 0 := by
  simp [← coeff_inj]

@[simp]
/--
theorem `single_add` / 定理 `single_add`

English:
theorem single_add
  given: (a : G) (b₁ b₂ : k)
  statement: single a (b₁ + b₂) = single a b₁ + single a b₂
  proof: by
  simp [← coeff_inj]

@[simp]

中文:
定理 single_add
  条件: (a : G) (b₁ b₂ : k)
  结论: single a (b₁ + b₂) = single a b₁ + single a b₂
  证明: by
  simp [← coeff_inj]

@[simp]

Depends on / 依赖: coeff_inj
-/
theorem single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single a b₂ := by
  simp [← coeff_inj]

@[simp]
/--
theorem `single_zero` / 定理 `single_zero`

English:
theorem single_zero
  given: (a : G)
  statement: (single a 0 : SkewMonoidAlgebra k G) = 0
  proof: by
  simp [← coeff_inj]

中文:
定理 single_zero
  条件: (a : G)
  结论: (single a 0 : 斜幺半群代数 k G) = 0
  证明: by
  simp [← coeff_inj]

Depends on / 依赖: coeff_inj
-/
theorem single_zero (a : G) : (single a 0 : SkewMonoidAlgebra k G) = 0 := by
  simp [← coeff_inj]

/--
theorem `single_eq_zero` / 定理 `single_eq_zero`

English:
theorem single_eq_zero
  given: {a : G} {b : k}
  statement: single a b = 0 ↔ b = 0
  proof: by
  simp [← coeff_inj]

中文:
定理 single_eq_zero
  条件: {a : G} {b : k}
  结论: single a b = 0 ↔ b = 0
  证明: by
  simp [← coeff_inj]

Depends on / 依赖: coeff_inj
-/
theorem single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0 := by
  simp [← coeff_inj]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Group isomorphism between `SkewMonoidAlgebra k G` and `G →₀ k`. -/
@[simps apply symm_apply]
/--
Definition of `coeffAddEquiv` / `coeffAddEquiv` 的定义

English:
definition coeffAddEquiv
  signature: : SkewMonoidAlgebra k G ≃+ (G ->₀ k) where
  body: coeff
  invFun := ofCoeff
  map_add' := coeff_add

@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv := coeffAddEquiv
@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv_apply := coeffAddEquiv_apply
@[deprecated (since := "2026-07-04")]
alias toFinsuppAddEquiv_symm_apply := coe

中文:
定义 coeffAddEquiv
  签名: : 斜幺半群代数 k G ≃+ (G ->₀ k) where
  定义体: coeff
  invFun := ofCoeff
  map_add' := coeff_add

@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv := coeffAddEquiv
@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv_apply := coeffAddEquiv_apply
@[deprecated (since := "2026-07-04")]
alias toFinsuppAddEquiv_symm_apply := coe
-/
def coeffAddEquiv : SkewMonoidAlgebra k G ≃+ (G ->₀ k) where
  toFun := coeff
  invFun := ofCoeff
  map_add' := coeff_add

@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv := coeffAddEquiv
@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv_apply := coeffAddEquiv_apply
@[deprecated (since := "2026-07-04")]
alias toFinsuppAddEquiv_symm_apply := coeffAddEquiv_symm_apply

/--
theorem `smul_single` / 定理 `smul_single`

English:
theorem smul_single
  given: {S} [SMulZeroClass S k] (s : S) (a : G) (b : k)
  proof: coeff_injective by simp;

中文:
定理 smul_single
  条件: {S} [SMulZero类 S k] (s : S) (a : G) (b : k)
  证明: coeff_injective by simp;

Depends on / 依赖: coeff_injective
-/
theorem smul_single {S} [SMulZeroClass S k] (s : S) (a : G) (b : k) :
    s • single a b = single a (s • b) :=
coeff_injective by simp;

/--
theorem `single_injective` / 定理 `single_injective`

English:
theorem single_injective
  given: (a : G)
  statement: Function.Injective (single a : k -> SkewMonoidAlgebra k G)
  proof: coeffAddEquiv.symm.injective.comp (Finsupp.single_injective a)

中文:
定理 single_injective
  条件: (a : G)
  结论: 函数.单射 (single a : k -> 斜幺半群代数 k G)
  证明: coeffAddEquiv.symm.injective.comp (Finsupp.single_injective a)

Depends on / 依赖: Finsupp, Finsupp.single_injective, coeffAddEquiv, coeffAddEquiv.symm.injective.comp, injective, single_injective
-/
theorem single_injective (a : G) : Function.Injective (single a : k -> SkewMonoidAlgebra k G) :=
  coeffAddEquiv.symm.injective.comp (Finsupp.single_injective a)

/--
theorem `single_left_inj` / 定理 `single_left_inj`

English:
theorem single_left_inj
  given: {a a' : G} {b : k} (h : b != 0)
  statement: single a b = single a' b ↔ a = a'
  proof: by
  rw [← coeff_inj]
  exact Finsupp.single_left_inj h

中文:
定理 single_left_inj
  条件: {a a' : G} {b : k} (h : b != 0)
  结论: single a b = single a' b ↔ a = a'
  证明: by
  rw [← coeff_inj]
  exact Finsupp.single_left_inj h

Depends on / 依赖: Finsupp, Finsupp.single_left_inj, coeff_inj, single_left_inj
-/
theorem single_left_inj {a a' : G} {b : k} (h : b != 0) : single a b = single a' b ↔ a = a' := by
  rw [← coeff_inj]
  exact Finsupp.single_left_inj h

/--
theorem `_root_.IsSMulRegular.skewMonoidAlgebra_iff` / 定理 `_root_.IsSMulRegular.skewMonoidAlgebra_iff`

English:
theorem _root_.IsSMulRegular.skewMonoidAlgebra_iff
  statement: {S : Type*} [Monoid S] [DistribMulAction S k]
  proof: by
  inhabit G
  refine ⟨IsSMulRegular.skewMonoidAlgebra, fun ha b₁ b₂ inj => ?_⟩
  rw [← (single_injective _).eq_iff]; rw [← smul_single]; rw [← smul_single] at inj
  exact single_injective default (ha inj)

中文:
定理 _root_.IsSMulRegular.skewMonoidAlgebra_iff
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S k]
  证明: by
  inhabit G
  refine ⟨IsSMulRegular.skewMonoidAlgebra, fun ha b₁ b₂ inj => ?_⟩
  rw [← (single_injective _).eq_iff]; rw [← smul_single]; rw [← smul_single] at inj
  exact single_injective default (ha inj)

Depends on / 依赖: IsSMulRegular, IsSMulRegular.skewMonoidAlgebra, eq_iff, inhabit, single_injective, skewMonoidAlgebra, smul_single
-/
theorem _root_.IsSMulRegular.skewMonoidAlgebra_iff {S : Type*} [Monoid S] [DistribMulAction S k]
    {a : S} [Nonempty G] : IsSMulRegular k a ↔ IsSMulRegular (SkewMonoidAlgebra k G) a := by
  inhabit G
  refine ⟨IsSMulRegular.skewMonoidAlgebra, fun ha b₁ b₂ inj => ?_⟩
  rw [← (single_injective _).eq_iff]; rw [← smul_single]; rw [← smul_single] at inj
  exact single_injective default (ha inj)

end Single

end AddMonoid

section AddMonoidWithOne

section One

variable [One G] [AddMonoidWithOne k]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (SkewMonoidAlgebra k G)
  body: single 1 1

中文:
实例 :
  签名: 幺 (斜幺半群代数 k G)
  定义体: single 1 1

Depends on / 依赖: IsMinimal, IsMinimal.val_, single
-/
instance : One (SkewMonoidAlgebra k G) where
  one := single 1 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoidWithOne (SkewMonoidAlgebra k G)

中文:
实例 :
  签名: 加法带幺幺半群 (斜幺半群代数 k G)
-/
instance : AddMonoidWithOne (SkewMonoidAlgebra k G) where

/--
theorem `ofCoeff_one` / 定理 `ofCoeff_one`

English:
theorem ofCoeff_one
  statement: (⟨Finsupp.single 1 1⟩ : SkewMonoidAlgebra k G) = 1
  proof: rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_one := ofCoeff_one

@[simp]

中文:
定理 ofCoeff_one
  结论: (⟨有限支撑.single 1 1⟩ : 斜幺半群代数 k G) = 1
  证明: rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_one := ofCoeff_one

@[simp]
-/
theorem ofCoeff_one : (⟨Finsupp.single 1 1⟩ : SkewMonoidAlgebra k G) = 1 := rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_one := ofCoeff_one

@[simp]
/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  statement: (1 : SkewMonoidAlgebra k G).coeff = Finsupp.single 1 1
  proof: rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_one := coeff_one

@[simp]

中文:
定理 coeff_one
  结论: (1 : 斜幺半群代数 k G).coeff = 有限支撑.single 1 1
  证明: rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_one := coeff_one

@[simp]

Depends on / 依赖: W.exists_isMinimal, choose_spec, exists_isMinimal
-/
theorem coeff_one : (1 : SkewMonoidAlgebra k G).coeff = Finsupp.single 1 1 := rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_one := coeff_one

@[simp]
/--
theorem `coeff_eq_single_one_one_iff` / 定理 `coeff_eq_single_one_one_iff`

English:
theorem coeff_eq_single_one_one_iff
  given: {a : SkewMonoidAlgebra k G}
  proof: by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")]
alias toFinsupp_eq_single_one_one_iff := coeff_eq_single_one_one_iff

@[simp]

中文:
定理 coeff_eq_single_one_one_iff
  条件: {a : 斜幺半群代数 k G}
  证明: by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")]
alias toFinsupp_eq_single_one_one_iff := coeff_eq_single_one_one_iff

@[simp]

Depends on / 依赖: coeff_inj
-/
theorem coeff_eq_single_one_one_iff {a : SkewMonoidAlgebra k G} :
    a.coeff = Finsupp.single 1 1 ↔ a = 1 := by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")]
alias toFinsupp_eq_single_one_one_iff := coeff_eq_single_one_one_iff

@[simp]
/--
theorem `ofCoeff_eq_one` / 定理 `ofCoeff_eq_one`

English:
theorem ofCoeff_eq_one
  given: {a}
  proof: by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_one := ofCoeff_eq_one

@[simp]

中文:
定理 ofCoeff_eq_one
  条件: {a}
  证明: by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_one := ofCoeff_eq_one

@[simp]

Depends on / 依赖: coeff_inj
-/
theorem ofCoeff_eq_one {a} :
    (⟨a⟩ : SkewMonoidAlgebra k G) = 1 ↔ a = Finsupp.single 1 1 := by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_one := ofCoeff_eq_one

@[simp]
/--
theorem `single_one_one` / 定理 `single_one_one`

English:
theorem single_one_one
  statement: single (1 : G) (1 : k) = 1
  proof: rfl

中文:
定理 single_one_one
  结论: single (1 : G) (1 : k) = 1
  证明: rfl
-/
theorem single_one_one : single (1 : G) (1 : k) = 1 := rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : SkewMonoidAlgebra k G) = single 1 1
  proof: rfl

@[deprecated coeff_one (since := "2026-07-04")]

中文:
定理 one_def
  结论: (1 : 斜幺半群代数 k G) = single 1 1
  证明: rfl

@[deprecated coeff_one (since := "2026-07-04")]
-/
theorem one_def : (1 : SkewMonoidAlgebra k G) = single 1 1 := rfl

@[deprecated coeff_one (since := "2026-07-04")]
/--
theorem `coeff_one_one` / 定理 `coeff_one_one`

English:
theorem coeff_one_one
  statement: coeff (1 : SkewMonoidAlgebra k G) 1 = 1
  proof: by simp

中文:
定理 coeff_one_one
  结论: coeff (1 : 斜幺半群代数 k G) 1 = 1
  证明: by simp
-/
theorem coeff_one_one : coeff (1 : SkewMonoidAlgebra k G) 1 = 1 := by simp

/--
theorem `natCast_def` / 定理 `natCast_def`

English:
theorem natCast_def
  given: (n : Nat)
  statement: (n : SkewMonoidAlgebra k G) = single (1 : G) (n : k)
  proof: by
  induction n <;> simp_all

@[simp]

中文:
定理 natCast_def
  条件: (n : 自然数)
  结论: (n : 斜幺半群代数 k G) = single (1 : G) (n : k)
  证明: by
  induction n <;> simp_all

@[simp]
-/
theorem natCast_def (n : Nat) : (n : SkewMonoidAlgebra k G) = single (1 : G) (n : k) := by
  induction n <;> simp_all

@[simp]
/--
lemma `single_nat` / 引理 `single_nat`

English:
lemma single_nat
  given: (n : Nat)
  statement: (single 1 n : SkewMonoidAlgebra k G) = n
  proof: (natCast_def _).symm

中文:
引理 single_nat
  条件: (n : 自然数)
  结论: (single 1 n : 斜幺半群代数 k G) = n
  证明: (natCast_def _).symm

Depends on / 依赖: natCast_def
-/
lemma single_nat (n : Nat) : (single 1 n : SkewMonoidAlgebra k G) = n := (natCast_def _).symm

end One

end AddMonoidWithOne

section AddCommMonoid

variable [AddCommMonoid k]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (SkewMonoidAlgebra k G)
  body: coeff_injective.addCommMonoid _ coeff_zero coeff_add
    (fun _ _ => coeff_smul _ _)

中文:
实例 :
  签名: 加法交换幺半群 (斜幺半群代数 k G)
  定义体: coeff_injective.addCommMonoid _ coeff_zero coeff_add
    (fun _ _ => coeff_smul _ _)

Depends on / 依赖: addCommMonoid, coeff_add, coeff_injective, coeff_injective.addCommMonoid, coeff_zero
-/
instance : AddCommMonoid (SkewMonoidAlgebra k G) where
  __ := coeff_injective.addCommMonoid _ coeff_zero coeff_add
    (fun _ _ => coeff_smul _ _)

section sum

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: G] [DecidableEq k] : DecidableEq (SkewMonoidAlgebra k G)
  body: Equiv.decidableEq coeffAddEquiv.toEquiv

中文:
实例 [DecidableEq
  签名: G] [DecidableEq k] : DecidableEq (斜幺半群代数 k G)
  定义体: Equiv.decidableEq coeffAddEquiv.toEquiv

Depends on / 依赖: Equiv.decidableEq, coeffAddEquiv, coeffAddEquiv.toEquiv, decidableEq, toEquiv
-/
instance [DecidableEq G] [DecidableEq k] : DecidableEq (SkewMonoidAlgebra k G) :=
  Equiv.decidableEq coeffAddEquiv.toEquiv

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k -> N)
  body: f.coeff.sum g

中文:
定义 求和
  签名: {N : 类型} [加法交换幺半群 N] (f : 斜幺半群代数 k G) (g : G -> k -> N)
  定义体: f.coeff.sum g

Depends on / 依赖: f.coeff.sum
-/
def sum {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k -> N) : N :=
  f.coeff.sum g

/--
theorem `sum_def` / 定理 `sum_def`

English:
theorem sum_def
  given: {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k -> N)
  proof: rfl

中文:
定理 sum_def
  条件: {N : 类型} [加法交换幺半群 N] (f : 斜幺半群代数 k G) (g : G -> k -> N)
  证明: rfl
-/
theorem sum_def {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k -> N) :
    sum f g = f.coeff.sum g := rfl

/--
theorem `sum_def'` / 定理 `sum_def'`

English:
theorem sum_def'
  given: {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k -> N)
  proof: rfl

@[simp]

中文:
定理 sum_def'
  条件: {N : 类型} [加法交换幺半群 N] (f : 斜幺半群代数 k G) (g : G -> k -> N)
  证明: rfl

@[simp]
-/
theorem sum_def' {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k -> N) :
    sum f g = ∑ a in f.support, g a (f.coeff a) := rfl

@[simp]
/--
theorem `sum_single_index` / 定理 `sum_single_index`

English:
theorem sum_single_index
  statement: {N} [AddCommMonoid N] {a : G} {b : k} {h : G -> k -> N}
  proof: Finsupp.sum_single_index h_zero

中文:
定理 sum_single_index
  结论: {N} [加法交换幺半群 N] {a : G} {b : k} {h : G -> k -> N}
  证明: Finsupp.sum_single_index h_zero

Depends on / 依赖: Finsupp, Finsupp.sum_single_index, h_zero, sum_single_index
-/
theorem sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G -> k -> N}
    (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.single a b).sum h = h a b :=
  Finsupp.sum_single_index h_zero

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  statement: {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [FunLike H N P]
  proof: _root_.map_sum h _ _

中文:
定理 map_sum
  结论: {N P : 类型} [加法交换幺半群 N] [加法交换幺半群 P] {H : 类型} [函数状 H N P]
  证明: _root_.map_sum h _ _

Depends on / 依赖: _root_, _root_.map_sum, map_sum
-/
theorem map_sum {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [FunLike H N P]
    [AddMonoidHomClass H N P] (h : H) (f : SkewMonoidAlgebra k G) (g : G -> k -> N) :
    h (sum f g) = sum f fun a b => h (g a b) :=
  _root_.map_sum h _ _

/--
theorem `coeff_sum'` / 定理 `coeff_sum'`

English:
theorem coeff_sum'
  statement: {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G)
  proof: _root_.map_sum coeffAddEquiv (fun a => g a (f.coeff a)) f.coeff.support

@[deprecated (since := "2026-07-04")] alias toFinsupp_sum' := coeff_sum'

中文:
定理 coeff_sum'
  结论: {k' G' : 类型} [加法交换幺半群 k'] (f : 斜幺半群代数 k G)
  证明: _root_.map_sum coeffAddEquiv (fun a => g a (f.coeff a)) f.coeff.support

@[deprecated (since := "2026-07-04")] alias toFinsupp_sum' := coeff_sum'

Depends on / 依赖: _root_, _root_.map_sum, coeffAddEquiv, f.coeff, f.coeff.support, map_sum, support
-/
theorem coeff_sum' {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G)
    (g : G -> k -> SkewMonoidAlgebra k' G') :
    (sum f g).coeff = Finsupp.sum f.coeff (coeff <| g · ·) :=
  _root_.map_sum coeffAddEquiv (fun a => g a (f.coeff a)) f.coeff.support

@[deprecated (since := "2026-07-04")] alias toFinsupp_sum' := coeff_sum'

/--
theorem `ofCoeff_sum` / 定理 `ofCoeff_sum`

English:
theorem ofCoeff_sum
  statement: {k' G' : Type*} [AddCommMonoid k'] (f : G ->₀ k)
  proof: by
  apply coeff_injective; simp only [coeff_sum']

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sum := ofCoeff_sum

中文:
定理 ofCoeff_sum
  结论: {k' G' : 类型} [加法交换幺半群 k'] (f : G ->₀ k)
  证明: by
  apply coeff_injective; simp only [coeff_sum']

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sum := ofCoeff_sum

Depends on / 依赖: coeff_injective, coeff_sum
-/
theorem ofCoeff_sum {k' G' : Type*} [AddCommMonoid k'] (f : G ->₀ k)
    (g : G -> k -> G' ->₀ k') :
    (⟨Finsupp.sum f g⟩ : SkewMonoidAlgebra k' G') = sum ⟨f⟩ (⟨g · ·⟩) := by
  apply coeff_injective; simp only [coeff_sum']

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sum := ofCoeff_sum

/--
theorem `sum_single` / 定理 `sum_single`

English:
theorem sum_single
  given: (f : SkewMonoidAlgebra k G)
  statement: f.sum single = f
  proof: by
  apply coeff_injective; simp only [coeff_sum', coeff_single, Finsupp.sum_single]

中文:
定理 sum_single
  条件: (f : 斜幺半群代数 k G)
  结论: f.求和 single = f
  证明: by
  apply coeff_injective; simp only [coeff_sum', coeff_single, Finsupp.sum_single]

Depends on / 依赖: Finsupp, Finsupp.sum_single, coeff_injective, coeff_single, coeff_sum, sum_single
-/
theorem sum_single (f : SkewMonoidAlgebra k G) : f.sum single = f := by
  apply coeff_injective; simp only [coeff_sum', coeff_single, Finsupp.sum_single]

/--
theorem `sum_add_index'` / 定理 `sum_add_index'`

English:
theorem sum_add_index'
  statement: {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G -> k -> S}
  proof: by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add]; rw [eta]]
  exact Finsupp.sum_add_index' hf h_add

中文:
定理 sum_add_index'
  结论: {S : 类型} [加法交换幺半群 S] {f g : 斜幺半群代数 k G} {h : G -> k -> S}
  证明: by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add]; rw [eta]]
  exact Finsupp.sum_add_index' hf h_add

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, f.coeff, g.coeff, h_add, ofCoeff_add, sum_add_index
-/
theorem sum_add_index' {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G -> k -> S}
    (hf : forall i, h i 0 = 0) (h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add]; rw [eta]]
  exact Finsupp.sum_add_index' hf h_add

/--
theorem `sum_add_index` / 定理 `sum_add_index`

English:
theorem sum_add_index
  statement: {S : Type*} [DecidableEq G] [AddCommMonoid S]
  proof: by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add]; rw [eta]]
  exact Finsupp.sum_add_index h_zero h_add

@[simp]

中文:
定理 sum_add_index
  结论: {S : 类型} [DecidableEq G] [加法交换幺半群 S]
  证明: by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add]; rw [eta]]
  exact Finsupp.sum_add_index h_zero h_add

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, f.coeff, g.coeff, h_add, h_zero, ofCoeff_add, sum_add_index
-/
theorem sum_add_index {S : Type*} [DecidableEq G] [AddCommMonoid S]
    {f g : SkewMonoidAlgebra k G} {h : G -> k -> S} (h_zero : forall a in f.support union g.support, h a 0 = 0)
    (h_add : forall a in f.support union g.support, forall b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add]; rw [eta]]
  exact Finsupp.sum_add_index h_zero h_add

@[simp]
/--
theorem `sum_add` / 定理 `sum_add`

English:
theorem sum_add
  given: {S : Type*} [AddCommMonoid S] (p : SkewMonoidAlgebra k G) (f g : G -> k -> S)
  proof: Finsupp.sum_add

@[simp]

中文:
定理 sum_add
  条件: {S : 类型} [加法交换幺半群 S] (p : 斜幺半群代数 k G) (f g : G -> k -> S)
  证明: Finsupp.sum_add

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_add, sum_add
-/
theorem sum_add {S : Type*} [AddCommMonoid S] (p : SkewMonoidAlgebra k G) (f g : G -> k -> S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g := Finsupp.sum_add

@[simp]
/--
theorem `sum_zero_index` / 定理 `sum_zero_index`

English:
theorem sum_zero_index
  given: {S : Type*} [AddCommMonoid S] {f : G -> k -> S}
  proof: by simp [sum]

@[simp]

中文:
定理 sum_zero_index
  条件: {S : 类型} [加法交换幺半群 S] {f : G -> k -> S}
  证明: by simp [sum]

@[simp]
-/
theorem sum_zero_index {S : Type*} [AddCommMonoid S] {f : G -> k -> S} :
    (0 : SkewMonoidAlgebra k G).sum f = 0 := by simp [sum]

@[simp]
/--
theorem `sum_zero` / 定理 `sum_zero`

English:
theorem sum_zero
  given: {N : Type*} [AddCommMonoid N] {f : SkewMonoidAlgebra k G}
  proof: Finset.sum_const_zero

中文:
定理 sum_zero
  条件: {N : 类型} [加法交换幺半群 N] {f : 斜幺半群代数 k G}
  证明: Finset.sum_const_zero

Depends on / 依赖: Finset, Finset.sum_const_zero, sum_const_zero
-/
theorem sum_zero {N : Type*} [AddCommMonoid N] {f : SkewMonoidAlgebra k G} :
    (f.sum fun _ _ => (0 : N)) = 0 := Finset.sum_const_zero

/--
theorem `sum_sum_index` / 定理 `sum_sum_index`

English:
theorem sum_sum_index
  statement: {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  proof: by
  rw [sum_def]; rw [coeff_sum' f g]; rw [Finsupp.sum_sum_index h_zero h_add]; simp [sum_def]

@[simp]

中文:
定理 sum_sum_index
  结论: {α β M N P : 类型} [加法交换幺半群 M] [加法交换幺半群 N] [加法交换幺半群 P]
  证明: by
  rw [sum_def]; rw [coeff_sum' f g]; rw [Finsupp.sum_sum_index h_zero h_add]; simp [sum_def]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_sum_index, coeff_sum, h_add, h_zero, sum_def, sum_sum_index
-/
theorem sum_sum_index {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    {f : SkewMonoidAlgebra M α} {g : α -> M -> SkewMonoidAlgebra N β} {h : β -> N -> P}
    (h_zero : forall (a : β), h a 0 = 0)
    (h_add : forall (a : β) (b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun a b => sum (g a b) h := by
  rw [sum_def]; rw [coeff_sum' f g]; rw [Finsupp.sum_sum_index h_zero h_add]; simp [sum_def]

@[simp]
/--
theorem `coeff_sum` / 定理 `coeff_sum`

English:
theorem coeff_sum
  statement: {k' G' : Type*} [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
  proof: by
  simp_rw [coeff_sum', sum_def, Finsupp.sum_apply]

中文:
定理 coeff_sum
  结论: {k' G' : 类型} [加法交换幺半群 k'] {f : 斜幺半群代数 k G}
  证明: by
  simp_rw [coeff_sum', sum_def, Finsupp.sum_apply]

Depends on / 依赖: Finsupp, Finsupp.sum_apply, coeff_sum, simp_rw, sum_apply, sum_def
-/
theorem coeff_sum {k' G' : Type*} [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G -> k -> SkewMonoidAlgebra k' G'} {a₂ : G'} :
    (f.sum g).coeff a₂ = f.sum fun a₁ b => (g a₁ b).coeff a₂ := by
  simp_rw [coeff_sum', sum_def, Finsupp.sum_apply]

/--
theorem `sum_mul` / 定理 `sum_mul`

English:
theorem sum_mul
  statement: {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
  proof: by
  simp only [sum, Finsupp.sum, Finset.sum_mul]

中文:
定理 sum_mul
  结论: {S : 类型} [非幺非结合半环 S] (b : S) (s : 斜幺半群代数 k G)
  证明: by
  simp only [sum, Finsupp.sum, Finset.sum_mul]

Depends on / 依赖: Finset, Finset.sum_mul, Finsupp, Finsupp.sum, sum_mul
-/
theorem sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G -> k -> S} : s.sum f * b = s.sum fun a c => f a c * b := by
  simp only [sum, Finsupp.sum, Finset.sum_mul]

/--
theorem `mul_sum` / 定理 `mul_sum`

English:
theorem mul_sum
  statement: {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
  proof: by
  simp only [sum, Finsupp.sum, Finset.mul_sum]

中文:
定理 mul_sum
  结论: {S : 类型} [非幺非结合半环 S] (b : S) (s : 斜幺半群代数 k G)
  证明: by
  simp only [sum, Finsupp.sum, Finset.mul_sum]

Depends on / 依赖: Finset, Finset.mul_sum, Finsupp, Finsupp.sum, mul_sum
-/
theorem mul_sum {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G -> k -> S} : b * s.sum f = s.sum fun a c => b * f a c := by
  simp only [sum, Finsupp.sum, Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
/-- Analogue of `Finsupp.sum_ite_eq'` for `SkewMonoidAlgebra`. -/
@[simp]
/--
theorem `sum_ite_eq'` / 定理 `sum_ite_eq'`

English:
theorem sum_ite_eq'
  statement: {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
  proof: by
  simp only [sum_def', f.coeff.support.sum_ite_eq', support]

中文:
定理 sum_ite_eq'
  结论: {N : 类型} [加法交换幺半群 N] [DecidableEq G] (f : 斜幺半群代数 k G)
  证明: by
  simp only [sum_def', f.coeff.support.sum_ite_eq', support]

Depends on / 依赖: f.coeff.support.sum_ite_eq, sum_def, sum_ite_eq, support
-/
theorem sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
    (a : G) (b : G -> k -> N) : (f.sum fun (x : G) (v : k) => if x = a then b x v else 0) =
      if a in f.support then b a (f.coeff a) else 0 := by
  simp only [sum_def', f.coeff.support.sum_ite_eq', support]

/--
theorem `smul_sum` / 定理 `smul_sum`

English:
theorem smul_sum
  statement: {M : Type*} {R : Type*} [AddCommMonoid M] [DistribSMul R M]
  proof: Finsupp.smul_sum

中文:
定理 smul_sum
  结论: {M : 类型} {R : 类型} [加法交换幺半群 M] [分配标量乘法 R M]
  证明: Finsupp.smul_sum

Depends on / 依赖: Finsupp, Finsupp.smul_sum, smul_sum
-/
theorem smul_sum {M : Type*} {R : Type*} [AddCommMonoid M] [DistribSMul R M]
    {v : SkewMonoidAlgebra k G} {c : R} {h : G -> k -> M} :
    c • v.sum h = v.sum fun a b => c • h a b := Finsupp.smul_sum

/--
theorem `sum_congr` / 定理 `sum_congr`

English:
theorem sum_congr
  statement: {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂ : G -> k -> M}
  proof: Finset.sum_congr rfl h

@[elab_as_elim]

中文:
定理 sum_congr
  结论: {f : 斜幺半群代数 k G} {M : 类型} [加法交换幺半群 M] {g₁ g₂ : G -> k -> M}
  证明: Finset.sum_congr rfl h

@[elab_as_elim]

Depends on / 依赖: Finset, Finset.sum_congr, sum_congr
-/
theorem sum_congr {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂ : G -> k -> M}
    (h : forall x in f.support, g₁ x (f.coeff x) = g₂ x (f.coeff x)) :
    f.sum g₁ = f.sum g₂ := Finset.sum_congr rfl h

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {p : SkewMonoidAlgebra k G -> Prop} (f : SkewMonoidAlgebra k G)
  proof: by
  rw [← sum_single f]; rw [sum_def']
  exact Finset.sum_induction _ _ add zero (by simp_all)

中文:
定理 induction_on
  结论: {p : 斜幺半群代数 k G -> 命题} (f : 斜幺半群代数 k G)
  证明: by
  rw [← sum_single f]; rw [sum_def']
  exact Finset.sum_induction _ _ add zero (by simp_all)

Depends on / 依赖: Finset, Finset.sum_induction, sum_def, sum_induction, sum_single
-/
theorem induction_on {p : SkewMonoidAlgebra k G -> Prop} (f : SkewMonoidAlgebra k G)
    (zero : p 0) (single : forall g a, p (single g a)) (add : forall f g :
    SkewMonoidAlgebra k G, p f -> p g -> p (f + g)) : p f := by
  rw [← sum_single f]; rw [sum_def']
  exact Finset.sum_induction _ _ add zero (by simp_all)

/-- Slightly less general but more convenient version of `SkewMonoidAlgebra.induction_on`. -/
@[induction_eliminator]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: [instNonempty : Nonempty G] {p : SkewMonoidAlgebra k G -> Prop}
  proof: induction_on f (by simpa using single (Classical.choice instNonempty) 0) single add

中文:
定理 induction_on'
  结论: [instNonempty : 非空 G] {p : 斜幺半群代数 k G -> 命题}
  证明: induction_on f (by simpa using single (Classical.choice instNonempty) 0) single add

Depends on / 依赖: Classical, Classical.choice, choice, induction_on, instNonempty, single
-/
theorem induction_on' [instNonempty : Nonempty G] {p : SkewMonoidAlgebra k G -> Prop}
    (f : SkewMonoidAlgebra k G) (single : forall g a, p (single g a)) (add : forall f g :
    SkewMonoidAlgebra k G, p f -> p g -> p (f + g)) : p f :=
  induction_on f (by simpa using single (Classical.choice instNonempty) 0) single add

/-- If two additive homomorphisms from `SkewMonoidAlgebra k G ` are equal on each `single a b`,
then they are equal. -/
@[ext high]
/--
theorem `addHom_ext` / 定理 `addHom_ext`

English:
theorem addHom_ext
  statement: {M : Type*} [AddZeroClass M] {f g : SkewMonoidAlgebra k G ->+ M}
  proof: by
  ext p; induction p using SkewMonoidAlgebra.induction_on <;> simp_all

中文:
定理 addHom_ext
  结论: {M : 类型} [加法零类 M] {f g : 斜幺半群代数 k G ->+ M}
  证明: by
  ext p; induction p using SkewMonoidAlgebra.induction_on <;> simp_all

Depends on / 依赖: SkewMonoidAlgebra, SkewMonoidAlgebra.induction_on, induction_on
-/
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : SkewMonoidAlgebra k G ->+ M}
    (h : forall a b, f (single a b) = g (single a b)) : f = g := by
  ext p; induction p using SkewMonoidAlgebra.induction_on <;> simp_all

end sum

section mapDomain

variable {G' G'' : Type*} (f : G -> G') {g : G' -> G''} (v : SkewMonoidAlgebra k G)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given `f : G → G'` and `v : SkewMonoidAlgebra k G`, `mapDomain f v : SkewMonoidAlgebra k G'`
is the finitely supported additive homomorphism whose value at `a : G'` is the sum of `v x` over
all `x` such that `f x = a`.
Note that `SkewMonoidAlgebra.mapDomain` is defined as an `AddHom`, while `MonoidAlgebra.mapDomain`
is defined as a function. -/
@[simps]
/--
Definition of `mapDomain` / `mapDomain` 的定义

English:
definition mapDomain
  signature: :
  body: v.sum fun a => single (f a)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ => single_zero _) fun _ => single_add _

中文:
定义 mapDomain
  签名: :
  定义体: v.sum fun a => single (f a)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ => single_zero _) fun _ => single_add _

Depends on / 依赖: single, v.sum
-/
def mapDomain :
    SkewMonoidAlgebra k G ->+ SkewMonoidAlgebra k G' where
  toFun v := v.sum fun a => single (f a)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ => single_zero _) fun _ => single_add _

/--
lemma `coeff_mapDomain` / 引理 `coeff_mapDomain`

English:
lemma coeff_mapDomain
  proof: by
  simp_rw [mapDomain_apply, Finsupp.mapDomain, coeff_sum', single]

@[deprecated (since := "2026-07-04")] alias toFinsupp_mapDomain := coeff_mapDomain

中文:
引理 coeff_mapDomain
  证明: by
  simp_rw [mapDomain_apply, Finsupp.mapDomain, coeff_sum', single]

@[deprecated (since := "2026-07-04")] alias toFinsupp_mapDomain := coeff_mapDomain

Depends on / 依赖: Finsupp, Finsupp.mapDomain, coeff_sum, mapDomain, mapDomain_apply, simp_rw, single
-/
lemma coeff_mapDomain :
    (mapDomain f v).coeff = Finsupp.mapDomain f v.coeff := by
  simp_rw [mapDomain_apply, Finsupp.mapDomain, coeff_sum', single]

@[deprecated (since := "2026-07-04")] alias toFinsupp_mapDomain := coeff_mapDomain

variable {f v}

/--
theorem `mapDomain_id` / 定理 `mapDomain_id`

English:
theorem mapDomain_id
  statement: mapDomain id v = v
  proof: sum_single _

中文:
定理 mapDomain_id
  结论: mapDomain id v = v
  证明: sum_single _

Depends on / 依赖: sum_single
-/
theorem mapDomain_id : mapDomain id v = v := sum_single _

/--
theorem `mapDomain_comp` / 定理 `mapDomain_comp`

English:
theorem mapDomain_comp
  statement: mapDomain (g ∘ f) v = mapDomain g (mapDomain f v)
  proof: ((sum_sum_index (single_zero <| g ·) (single_add <| g ·)).trans
    (sum_congr fun _ _ => sum_single_index (single_zero _))).symm

中文:
定理 mapDomain_comp
  结论: mapDomain (g ∘ f) v = mapDomain g (mapDomain f v)
  证明: ((sum_sum_index (single_zero <| g ·) (single_add <| g ·)).trans
    (sum_congr fun _ _ => sum_single_index (single_zero _))).symm

Depends on / 依赖: single_add, single_zero, sum_congr, sum_single_index, sum_sum_index
-/
theorem mapDomain_comp : mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) :=
  ((sum_sum_index (single_zero <| g ·) (single_add <| g ·)).trans
    (sum_congr fun _ _ => sum_single_index (single_zero _))).symm

/--
theorem `sum_mapDomain_index` / 定理 `sum_mapDomain_index`

English:
theorem sum_mapDomain_index
  statement: {k' : Type*} [AddCommMonoid k'] {h : G' -> k -> k'}
  proof: (sum_sum_index h_zero h_add).trans sum_congr fun _ _ => sum_single_index (h_zero _)

中文:
定理 sum_mapDomain_index
  结论: {k' : 类型} [加法交换幺半群 k'] {h : G' -> k -> k'}
  证明: (sum_sum_index h_zero h_add).trans sum_congr fun _ _ => sum_single_index (h_zero _)

Depends on / 依赖: h_add, h_zero, sum_congr, sum_single_index, sum_sum_index
-/
theorem sum_mapDomain_index {k' : Type*} [AddCommMonoid k'] {h : G' -> k -> k'}
    (h_zero : forall (b : G'), h b 0 = 0)
    (h_add : forall (b : G') (m₁ m₂ : k), h b (m₁ + m₂) = h b m₁ + h b m₂) :
    sum (mapDomain f v) h = sum v fun a m => h (f a) m :=
(sum_sum_index h_zero h_add).trans sum_congr fun _ _ => sum_single_index (h_zero _)

/--
theorem `mapDomain_single` / 定理 `mapDomain_single`

English:
theorem mapDomain_single
  given: {a : G} {b : k}
  statement: mapDomain f (single a b) = single (f a) b
  proof: sum_single_index single_zero _

中文:
定理 mapDomain_single
  条件: {a : G} {b : k}
  结论: mapDomain f (single a b) = single (f a) b
  证明: sum_single_index single_zero _

Depends on / 依赖: single_zero, sum_single_index
-/
theorem mapDomain_single {a : G} {b : k} : mapDomain f (single a b) = single (f a) b :=
sum_single_index single_zero _

/--
theorem `mapDomain_smul` / 定理 `mapDomain_smul`

English:
theorem mapDomain_smul
  given: {R : Type*} [Monoid R] [DistribMulAction R k] {b : R}
  proof: by
  simp_rw [← coeff_inj, coeff_smul, coeff_mapDomain]
  simp [Finsupp.mapDomain_smul]

中文:
定理 mapDomain_smul
  条件: {R : 类型} [幺半群 R] [分配乘法作用 R k] {b : R}
  证明: by
  simp_rw [← coeff_inj, coeff_smul, coeff_mapDomain]
  simp [Finsupp.mapDomain_smul]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_smul, coeff_inj, coeff_mapDomain, coeff_smul, mapDomain_smul, simp_rw
-/
theorem mapDomain_smul {R : Type*} [Monoid R] [DistribMulAction R k] {b : R} :
    mapDomain f (b • v) = b • mapDomain f v := by
  simp_rw [← coeff_inj, coeff_smul, coeff_mapDomain]
  simp [Finsupp.mapDomain_smul]

/--
Definition of `liftNC` / `liftNC` 的定义

English:
definition liftNC
  signature: {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R) (g : G -> R)
  body: (Finsupp.liftAddHom fun x => (AddMonoidHom.mulRight (g x)).comp f).comp
    (AddEquiv.toAddMonoidHom coeffAddEquiv)

中文:
定义 liftNC
  签名: {R : 类型} [非幺非结合半环 R] (f : k ->+ R) (g : G -> R)
  定义体: (Finsupp.liftAddHom fun x => (AddMonoidHom.mulRight (g x)).comp f).comp
    (AddEquiv.toAddMonoidHom coeffAddEquiv)

Depends on / 依赖: AddEquiv, AddEquiv.toAddMonoidHom, AddMonoidHom, AddMonoidHom.mulRight, Finsupp, Finsupp.liftAddHom, coeffAddEquiv, liftAddHom, mulRight, toAddMonoidHom
-/
def liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R) (g : G -> R) :
    SkewMonoidAlgebra k G ->+ R :=
  (Finsupp.liftAddHom fun x => (AddMonoidHom.mulRight (g x)).comp f).comp
    (AddEquiv.toAddMonoidHom coeffAddEquiv)

/--
theorem `liftNC_single` / 定理 `liftNC_single`

English:
theorem liftNC_single
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R)
  proof: Finsupp.liftAddHom_apply_single _ _ _

中文:
定理 liftNC_single
  结论: {R : 类型} [非幺非结合半环 R] (f : k ->+ R)
  证明: Finsupp.liftAddHom_apply_single _ _ _
-/
@[simp] theorem liftNC_single {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R)
    (g : G -> R) (a : G) (b : k) : liftNC f g (single a b) = f b * g a :=
  Finsupp.liftAddHom_apply_single _ _ _

/--
theorem `eq_liftNC` / 定理 `eq_liftNC`

English:
theorem eq_liftNC
  statement: {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R) (g : G -> R)
  proof: by
  ext a b; simp_all

中文:
定理 eq_liftNC
  结论: {R : 类型} [非幺非结合半环 R] (f : k ->+ R) (g : G -> R)
  证明: by
  ext a b; simp_all
-/
theorem eq_liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R) (g : G -> R)
    (l : SkewMonoidAlgebra k G ->+ R) (h : forall a b, l (single a b) = f b * g a) : l = liftNC f g := by
  ext a b; simp_all

end mapDomain

end AddCommMonoid

section AddGroup

variable [AddGroup k]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (SkewMonoidAlgebra k G)
  body: ⟨fun ⟨a⟩ => ⟨-a⟩⟩

@[simp]

中文:
实例 :
  签名: 取负 (斜幺半群代数 k G)
  定义体: ⟨fun ⟨a⟩ => ⟨-a⟩⟩

@[simp]
-/
@[no_expose] instance : Neg (SkewMonoidAlgebra k G) :=
  ⟨fun ⟨a⟩ => ⟨-a⟩⟩

@[simp]
/--
theorem `ofCoeff_neg` / 定理 `ofCoeff_neg`

English:
theorem ofCoeff_neg
  given: {a}
  statement: (⟨-a⟩ : SkewMonoidAlgebra k G) = -⟨a⟩
  proof: (rfl)

@[deprecated (since := "2026-07-04")] alias ofFinsupp_neg := ofCoeff_neg

中文:
定理 ofCoeff_neg
  条件: {a}
  结论: (⟨-a⟩ : 斜幺半群代数 k G) = -⟨a⟩
  证明: (rfl)

@[deprecated (since := "2026-07-04")] alias ofFinsupp_neg := ofCoeff_neg
-/
theorem ofCoeff_neg {a} : (⟨-a⟩ : SkewMonoidAlgebra k G) = -⟨a⟩ :=
  (rfl)

@[deprecated (since := "2026-07-04")] alias ofFinsupp_neg := ofCoeff_neg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroup (SkewMonoidAlgebra k G)
  body: zsmulRec
  neg_add_cancel a := by cases a; simp [← ofCoeff_neg, ← ofCoeff_add]

@[simp]

中文:
实例 :
  签名: 加法群 (斜幺半群代数 k G)
  定义体: zsmulRec
  neg_add_cancel a := by cases a; simp [← ofCoeff_neg, ← ofCoeff_add]

@[simp]

Depends on / 依赖: zsmulRec
-/
instance : AddGroup (SkewMonoidAlgebra k G) where
  zsmul := zsmulRec
  neg_add_cancel a := by cases a; simp [← ofCoeff_neg, ← ofCoeff_add]

@[simp]
/--
theorem `coeff_neg` / 定理 `coeff_neg`

English:
theorem coeff_neg
  given: (a : SkewMonoidAlgebra k G)
  statement: (-a).coeff = -a.coeff
  proof: coeffAddEquiv.map_neg a

@[deprecated (since := "2026-07-04")] alias toFinsupp_neg := coeff_neg

@[simp]

中文:
定理 coeff_neg
  条件: (a : 斜幺半群代数 k G)
  结论: (-a).coeff = -a.coeff
  证明: coeffAddEquiv.map_neg a

@[deprecated (since := "2026-07-04")] alias toFinsupp_neg := coeff_neg

@[simp]

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.map_neg, map_neg
-/
theorem coeff_neg (a : SkewMonoidAlgebra k G) : (-a).coeff = -a.coeff :=
  coeffAddEquiv.map_neg a

@[deprecated (since := "2026-07-04")] alias toFinsupp_neg := coeff_neg

@[simp]
/--
theorem `ofCoeff_sub` / 定理 `ofCoeff_sub`

English:
theorem ofCoeff_sub
  given: {a b}
  statement: (⟨a - b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ - ⟨b⟩
  proof: coeffAddEquiv.symm.map_sub a b

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sub := ofCoeff_sub

@[simp]

中文:
定理 ofCoeff_sub
  条件: {a b}
  结论: (⟨a - b⟩ : 斜幺半群代数 k G) = ⟨a⟩ - ⟨b⟩
  证明: coeffAddEquiv.symm.map_sub a b

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sub := ofCoeff_sub

@[simp]

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.symm.map_sub, map_sub
-/
theorem ofCoeff_sub {a b} : (⟨a - b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ - ⟨b⟩ :=
  coeffAddEquiv.symm.map_sub a b

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sub := ofCoeff_sub

@[simp]
/--
theorem `coeff_sub` / 定理 `coeff_sub`

English:
theorem coeff_sub
  given: (a b : SkewMonoidAlgebra k G)
  proof: coeffAddEquiv.map_sub a b

@[deprecated (since := "2026-07-04")] alias toFinsupp_sub := coeff_sub

@[simp]

中文:
定理 coeff_sub
  条件: (a b : 斜幺半群代数 k G)
  证明: coeffAddEquiv.map_sub a b

@[deprecated (since := "2026-07-04")] alias toFinsupp_sub := coeff_sub

@[simp]

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.map_sub, map_sub
-/
theorem coeff_sub (a b : SkewMonoidAlgebra k G) :
    (a - b).coeff = a.coeff - b.coeff :=
  coeffAddEquiv.map_sub a b

@[deprecated (since := "2026-07-04")] alias toFinsupp_sub := coeff_sub

@[simp]
/--
theorem `single_neg` / 定理 `single_neg`

English:
theorem single_neg
  given: (a : G) (b : k)
  statement: single a (-b) = -single a b
  proof: by
  simp [← ofCoeff_single]

中文:
定理 single_neg
  条件: (a : G) (b : k)
  结论: single a (-b) = -single a b
  证明: by
  simp [← ofCoeff_single]

Depends on / 依赖: ofCoeff_single
-/
theorem single_neg (a : G) (b : k) : single a (-b) = -single a b := by
  simp [← ofCoeff_single]

end AddGroup

section AddCommGroup

variable [AddCommGroup k]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (SkewMonoidAlgebra k G)

中文:
实例 :
  签名: 加法交换群 (斜幺半群代数 k G)
-/
instance : AddCommGroup (SkewMonoidAlgebra k G) where
  add_comm

end AddCommGroup

section AddGroupWithOne

variable [AddGroupWithOne k] [One G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroupWithOne (SkewMonoidAlgebra k G)
  body: instAddGroup

中文:
实例 :
  签名: 加法带幺群 (斜幺半群代数 k G)
  定义体: instAddGroup

Depends on / 依赖: instAddGroup
-/
instance : AddGroupWithOne (SkewMonoidAlgebra k G) where
  __ := instAddGroup

/--
theorem `intCast_def` / 定理 `intCast_def`

English:
theorem intCast_def
  given: (z : Int)
  statement: (z : SkewMonoidAlgebra k G) = single (1 : G) (z : k)
  proof: by
  cases z <;> simp

中文:
定理 intCast_def
  条件: (z : 整数)
  结论: (z : 斜幺半群代数 k G) = single (1 : G) (z : k)
  证明: by
  cases z <;> simp
-/
theorem intCast_def (z : Int) : (z : SkewMonoidAlgebra k G) = single (1 : G) (z : k) := by
  cases z <;> simp

end AddGroupWithOne

section Mul

/--
theorem `sum_smul_index` / 定理 `sum_smul_index`

English:
theorem sum_smul_index
  statement: {N : Type*} [AddCommMonoid N] [NonUnitalNonAssocSemiring k]
  proof: by
  simp [sum_def, Finsupp.sum_smul_index' h0]

中文:
定理 sum_smul_index
  结论: {N : 类型} [加法交换幺半群 N] [非幺非结合半环 k]
  证明: by
  simp [sum_def, Finsupp.sum_smul_index' h0]

Depends on / 依赖: Finsupp, Finsupp.sum_smul_index, sum_def, sum_smul_index
-/
theorem sum_smul_index {N : Type*} [AddCommMonoid N] [NonUnitalNonAssocSemiring k]
    {g : SkewMonoidAlgebra k G} {b : k} {h : G -> k -> N} (h0 : forall i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b * ·) := by
  simp [sum_def, Finsupp.sum_smul_index' h0]

/--
theorem `sum_smul_index'` / 定理 `sum_smul_index'`

English:
theorem sum_smul_index'
  statement: {N R : Type*} [AddCommMonoid k]
  proof: by
  simp only [sum_def, coeff_smul, Finsupp.sum_smul_index' h0]

@[simp]

中文:
定理 sum_smul_index'
  结论: {N R : 类型} [加法交换幺半群 k]
  证明: by
  simp only [sum_def, coeff_smul, Finsupp.sum_smul_index' h0]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_smul_index, coeff_smul, sum_def, sum_smul_index
-/
theorem sum_smul_index' {N R : Type*} [AddCommMonoid k]
    [DistribSMul R k] [AddCommMonoid N]
    {g : SkewMonoidAlgebra k G} {b : R} {h : G -> k -> N} (h0 : forall i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b • ·) := by
  simp only [sum_def, coeff_smul, Finsupp.sum_smul_index' h0]

@[simp]
/--
theorem `liftNC_one` / 定理 `liftNC_one`

English:
theorem liftNC_one
  statement: {g_hom R : Type*} [NonAssocSemiring k] [One G] [Semiring R] [FunLike g_hom G R]
  proof: by
  simp only [one_def, liftNC_single, AddMonoidHom.coe_coe, map_one, mul_one]

中文:
定理 liftNC_one
  结论: {g_hom R : 类型} [非结合半环 k] [幺 G] [半环 R] [函数状 g_hom G R]
  证明: by
  simp only [one_def, liftNC_single, AddMonoidHom.coe_coe, map_one, mul_one]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, coe_coe, liftNC_single, map_one, mul_one, one_def
-/
theorem liftNC_one {g_hom R : Type*} [NonAssocSemiring k] [One G] [Semiring R] [FunLike g_hom G R]
    [OneHomClass g_hom G R] (f : k ->+* R) (g : g_hom) : liftNC (f : k ->+ R) g 1 = 1 := by
  simp only [one_def, liftNC_single, AddMonoidHom.coe_coe, map_one, mul_one]

end Mul

section Mul

variable [Mul G]

section SMul

variable [SMul G k] [NonUnitalNonAssocSemiring k]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (SkewMonoidAlgebra k G)
  body: ⟨fun f g => f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂))⟩

中文:
实例 :
  签名: 乘法 (斜幺半群代数 k G)
  定义体: ⟨fun f g => f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂))⟩

Depends on / 依赖: f.sum, g.sum, single
-/
instance : Mul (SkewMonoidAlgebra k G) :=
  ⟨fun f g => f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂))⟩

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: {f g : SkewMonoidAlgebra k G}
  proof: rfl

中文:
定理 mul_def
  条件: {f g : 斜幺半群代数 k G}
  证明: rfl
-/
theorem mul_def {f g : SkewMonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂)) :=
  rfl

end SMul

section DistribSMul

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring k] [DistribSMul G k]
  body: by
    classical
    simp only [mul_def]
    refine Eq.trans (congr_arg (sum f) (funext₂ fun _ _ => sum_add_index ?_ ?_)) ?_ <;>
      simp only [smul_zero, smul_add, mul_add, mul_zero, single_zero, single_add,
        forall_true_iff, sum_add]
  right_distrib f g h := by
    classical
    simp only

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [非幺非结合半环 k] [分配标量乘法 G k]
  定义体: by
    classical
    simp only [mul_def]
    refine Eq.trans (congr_arg (sum f) (funext₂ fun _ _ => sum_add_index ?_ ?_)) ?_ <;>
      simp only [smul_zero, smul_add, mul_add, mul_zero, single_zero, single_add,
        forall_true_iff, sum_add]
  right_distrib f g h := by
    classical
    simp only

Depends on / 依赖: Eq.trans, add_mul, classical, congr_arg, forall_true_iff, mul_add, mul_def, mul_zero, right_distrib, single_add, single_zero, smul_add, smul_zero, sum_add, sum_add_index, sum_zero, sum_zero_index, zero_mul
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring k] [DistribSMul G k] :
    NonUnitalNonAssocSemiring (SkewMonoidAlgebra k G) where
  left_distrib f g h := by
    classical
    simp only [mul_def]
    refine Eq.trans (congr_arg (sum f) (funext₂ fun _ _ => sum_add_index ?_ ?_)) ?_ <;>
      simp only [smul_zero, smul_add, mul_add, mul_zero, single_zero, single_add,
        forall_true_iff, sum_add]
  right_distrib f g h := by
    classical
    simp only [mul_def]
    refine Eq.trans (sum_add_index ?_ ?_) ?_ <;>
      simp only [add_mul, zero_mul, single_zero, single_add, forall_true_iff, sum_zero, sum_add]
  zero_mul f := sum_zero_index
  mul_zero f := Eq.trans (congr_arg (sum f) (funext₂ fun _ _ => sum_zero_index)) sum_zero

variable {R : Type*} [Semiring R] [NonAssocSemiring k] [SMul G k]

/--
theorem `liftNC_mul` / 定理 `liftNC_mul`

English:
theorem liftNC_mul
  statement: {g_hom : Type*} [FunLike g_hom G R]
  proof: by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_sum, liftNC_single, sum_mul, mul_sum]
  refine sum_congr fun y hy => sum_congr fun x _hx => ?_
  simp only [AddMonoidHom.coe_coe, map_mul]
  rw [mul_assoc]; rw [← mul_assoc (f (y • b.coeff x))]; rw [h_comm hy]; rw [mul_asso

中文:
定理 liftNC_mul
  结论: {g_hom : 类型} [函数状 g_hom G R]
  证明: by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_sum, liftNC_single, sum_mul, mul_sum]
  refine sum_congr fun y hy => sum_congr fun x _hx => ?_
  simp only [AddMonoidHom.coe_coe, map_mul]
  rw [mul_assoc]; rw [← mul_assoc (f (y • b.coeff x))]; rw [h_comm hy]; rw [mul_asso

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, b.coeff, coe_coe, conv_rhs, h_comm, liftNC_single, map_mul, map_sum, mul_assoc, mul_def, mul_sum, simp_rw, sum_congr, sum_mul, sum_single
-/
theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R]
    [MulHomClass g_hom G R] (f : k ->+* R) (g : g_hom) (a b : SkewMonoidAlgebra k G)
    (h_comm : forall {x y}, y in a.support -> (f (y • b.coeff x)) * g y = (g y) * (f (b.coeff x))) :
    liftNC (f : k ->+ R) g (a * b) = liftNC (f : k ->+ R) g a * liftNC (f : k ->+ R) g b := by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_sum, liftNC_single, sum_mul, mul_sum]
  refine sum_congr fun y hy => sum_congr fun x _hx => ?_
  simp only [AddMonoidHom.coe_coe, map_mul]
  rw [mul_assoc]; rw [← mul_assoc (f (y • b.coeff x))]; rw [h_comm hy]; rw [mul_assoc]; rw [mul_assoc]

end DistribSMul

end Mul

/-! #### Semiring structure -/

section Semiring

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

open MulSemiringAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalSemiring (SkewMonoidAlgebra k G)
  body: by
    induction f with
    | single x a => induction g with
      | single y b => induction h with
        | single z c => simp [mul_assoc, mul_smul, mul_def]
        | add => simp_all [mul_add]
      | add => simp_all [add_mul, mul_add]
    | add => simp_all [add_mul]

中文:
实例 :
  签名: 非幺半环 (斜幺半群代数 k G)
  定义体: by
    induction f with
    | single x a => induction g with
      | single y b => induction h with
        | single z c => simp [mul_assoc, mul_smul, mul_def]
        | add => simp_all [mul_add]
      | add => simp_all [add_mul, mul_add]
    | add => simp_all [add_mul]

Depends on / 依赖: add_mul, mul_add, mul_assoc, mul_def, mul_smul, single
-/
instance : NonUnitalSemiring (SkewMonoidAlgebra k G) where
  mul_assoc f g h := by
    induction f with
    | single x a => induction g with
      | single y b => induction h with
        | single z c => simp [mul_assoc, mul_smul, mul_def]
        | add => simp_all [mul_add]
      | add => simp_all [add_mul, mul_add]
    | add => simp_all [add_mul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonAssocSemiring (SkewMonoidAlgebra k G)
  body: by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index] <;> simp
    | add f g _ _ => simp_all [mul_add]
  mul_one f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index, sum_single_index] <;> simp
    | add f g _ _ => simp_all [add_mul]

中文:
实例 :
  签名: 非结合半环 (斜幺半群代数 k G)
  定义体: by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index] <;> simp
    | add f g _ _ => simp_all [mul_add]
  mul_one f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index, sum_single_index] <;> simp
    | add f g _ _ => simp_all [add_mul]

Depends on / 依赖: add_mul, mul_add, mul_def, mul_one, one_def, single, sum_single_index
-/
instance : NonAssocSemiring (SkewMonoidAlgebra k G) where
  one_mul f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index] <;> simp
    | add f g _ _ => simp_all [mul_add]
  mul_one f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index, sum_single_index] <;> simp
    | add f g _ _ => simp_all [add_mul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (SkewMonoidAlgebra k G)
  body: instNonUnitalSemiring
  __ := instNonAssocSemiring

中文:
实例 :
  签名: 半环 (斜幺半群代数 k G)
  定义体: instNonUnitalSemiring
  __ := instNonAssocSemiring

Depends on / 依赖: instNonUnitalSemiring
-/
instance : Semiring (SkewMonoidAlgebra k G) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring

variable {R : Type*} [Semiring R]

/--
Definition of `liftNCRingHom` / `liftNCRingHom` 的定义

English:
definition liftNCRingHom
  signature: (f : k ->+* R) (g : G ->* R) (h_comm : forall {x y}, (f (y • x)) * g y = (g y) * (f x))
  body: liftNC (f : k ->+ R) g
  map_one' := liftNC_one _ _
  map_mul' _ _ := liftNC_mul _ _ _ _ fun {_ _} _ => h_comm

中文:
定义 liftNCRingHom
  签名: (f : k ->+* R) (g : G ->* R) (h_comm : 对任意 {x y}, (f (y • x)) * g y = (g y) * (f x))
  定义体: liftNC (f : k ->+ R) g
  map_one' := liftNC_one _ _
  map_mul' _ _ := liftNC_mul _ _ _ _ fun {_ _} _ => h_comm

Depends on / 依赖: liftNC
-/
def liftNCRingHom (f : k ->+* R) (g : G ->* R) (h_comm : forall {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra k G ->+* R where
  __ := liftNC (f : k ->+ R) g
  map_one' := liftNC_one _ _
  map_mul' _ _ := liftNC_mul _ _ _ _ fun {_ _} _ => h_comm

end Semiring

/-! #### Derived instances -/

section DerivedInstances

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [Ring k] [Monoid G] [MulSemiringAction G k]
  body: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

中文:
实例 instNonUnitalNonAssocRing
  签名: [环 k] [幺半群 G] [MulSemiring作用 G k]
  定义体: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

Depends on / 依赖: instAddCommGroup
-/
instance instNonUnitalNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonUnitalNonAssocRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [Ring k] [Monoid G] [MulSemiringAction G k]
  body: instAddCommGroup
  __ := instNonUnitalSemiring

中文:
实例 instNonUnitalRing
  签名: [环 k] [幺半群 G] [MulSemiring作用 G k]
  定义体: instAddCommGroup
  __ := instNonUnitalSemiring

Depends on / 依赖: instAddCommGroup
-/
instance instNonUnitalRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonUnitalRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonUnitalSemiring

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [Ring k] [Monoid G] [MulSemiringAction G k]
  body: instAddCommGroup
  __ := instNonAssocSemiring

中文:
实例 instNonAssocRing
  签名: [环 k] [幺半群 G] [MulSemiring作用 G k]
  定义体: instAddCommGroup
  __ := instNonAssocSemiring

Depends on / 依赖: instAddCommGroup
-/
instance instNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonAssocRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonAssocSemiring

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring k] [CommMonoid G] [MulSemiringAction G k]
  body: by
    have hgk (g : G) (r : k) : g • r = r := by
      rw [← Algebra.algebraMap_self_apply r]; rw [smul_algebraMap g r]
    simp only [mul_def, hgk, sum_def]
    rw [Finsupp.sum_comm]
    exact Finsupp.sum_congr (fun x _ => Finsupp.sum_congr
      (fun y _ => by rw [mul_comm, mul_comm (a.coeff y) _

中文:
实例 instCommSemiring
  签名: [交换半环 k] [交换幺半群 G] [MulSemiring作用 G k]
  定义体: by
    have hgk (g : G) (r : k) : g • r = r := by
      rw [← Algebra.algebraMap_self_apply r]; rw [smul_algebraMap g r]
    simp only [mul_def, hgk, sum_def]
    rw [Finsupp.sum_comm]
    exact Finsupp.sum_congr (fun x _ => Finsupp.sum_congr
      (fun y _ => by rw [mul_comm, mul_comm (a.coeff y) _

Depends on / 依赖: Algebra, Algebra.algebraMap_self_apply, Finsupp, Finsupp.sum_comm, Finsupp.sum_congr, a.coeff, algebraMap_self_apply, mul_comm, mul_def, smul_algebraMap, sum_comm, sum_congr, sum_def
-/
instance instCommSemiring [CommSemiring k] [CommMonoid G] [MulSemiringAction G k]
    [SMulCommClass G k k] : CommSemiring (SkewMonoidAlgebra k G) where
  mul_comm a b := by
    have hgk (g : G) (r : k) : g • r = r := by
      rw [← Algebra.algebraMap_self_apply r]; rw [smul_algebraMap g r]
    simp only [mul_def, hgk, sum_def]
    rw [Finsupp.sum_comm]
    exact Finsupp.sum_congr (fun x _ => Finsupp.sum_congr
      (fun y _ => by rw [mul_comm, mul_comm (a.coeff y) _]))

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Ring k] [Monoid G] [MulSemiringAction G k]
  body: instNonAssocRing
  __ := instSemiring

中文:
实例 instRing
  签名: [环 k] [幺半群 G] [MulSemiring作用 G k]
  定义体: instNonAssocRing
  __ := instSemiring

Depends on / 依赖: instNonAssocRing
-/
instance instRing [Ring k] [Monoid G] [MulSemiringAction G k] : Ring (SkewMonoidAlgebra k G) where
  __ := instNonAssocRing
  __ := instSemiring

variable {S S₁ S₂ : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: k] [DistribSMul S k] :
  body: coeff_injective.distribSMul ⟨⟨coeff, coeff_zero⟩, coeff_add⟩
    coeff_smul

中文:
实例 [加法幺半群
  签名: k] [分配标量乘法 S k] :
  定义体: coeff_injective.distribSMul ⟨⟨coeff, coeff_zero⟩, coeff_add⟩
    coeff_smul

Depends on / 依赖: coeff_add, coeff_injective, coeff_injective.distribSMul, coeff_zero, distribSMul
-/
instance [AddMonoid k] [DistribSMul S k] :
    DistribSMul S (SkewMonoidAlgebra k G) where
  __ := coeff_injective.distribSMul ⟨⟨coeff, coeff_zero⟩, coeff_add⟩
    coeff_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [AddMonoid k] [DistribMulAction S k] :
  body: coeff_injective.distribMulAction ⟨⟨coeff, coeff_zero (k := k)⟩, coeff_add⟩
      coeff_smul

中文:
实例 [幺半群
  签名: S] [加法幺半群 k] [分配乘法作用 S k] :
  定义体: coeff_injective.distribMulAction ⟨⟨coeff, coeff_zero (k := k)⟩, coeff_add⟩
      coeff_smul

Depends on / 依赖: coeff_add, coeff_injective, coeff_injective.distribMulAction, coeff_zero, distribMulAction
-/
instance [Monoid S] [AddMonoid k] [DistribMulAction S k] :
    DistribMulAction S (SkewMonoidAlgebra k G) where
  __ := coeff_injective.distribMulAction ⟨⟨coeff, coeff_zero (k := k)⟩, coeff_add⟩
      coeff_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [AddCommMonoid k] [Module S k] :
  body: coeff_injective.module _ ⟨⟨coeff, coeff_zero⟩, coeff_add⟩ coeff_smul

中文:
实例 [半环
  签名: S] [加法交换幺半群 k] [模 S k] :
  定义体: coeff_injective.module _ ⟨⟨coeff, coeff_zero⟩, coeff_add⟩ coeff_smul

Depends on / 依赖: coeff_add, coeff_injective, coeff_injective.module, coeff_smul, coeff_zero, module
-/
instance [Semiring S] [AddCommMonoid k] [Module S k] :
    Module S (SkewMonoidAlgebra k G) where
  __ := coeff_injective.module _ ⟨⟨coeff, coeff_zero⟩, coeff_add⟩ coeff_smul

/--
Instance `instFaithfulSMul` / 实例 `instFaithfulSMul`

English:
instance instFaithfulSMul
  signature: [AddMonoid k] [SMulZeroClass S k] [FaithfulSMul S k] [Nonempty G]
  body: by
    apply eq_of_smul_eq_smul fun a : G ->₀ k => congr_arg coeff _
    intro a
    simp_rw [ofCoeff_smul, h]

中文:
实例 instFaithfulSMul
  签名: [加法幺半群 k] [SMulZero类 S k] [忠实标量乘法 S k] [非空 G]
  定义体: by
    apply eq_of_smul_eq_smul fun a : G ->₀ k => congr_arg coeff _
    intro a
    simp_rw [ofCoeff_smul, h]

Depends on / 依赖: congr_arg, eq_of_smul_eq_smul, ofCoeff_smul, simp_rw
-/
instance instFaithfulSMul [AddMonoid k] [SMulZeroClass S k] [FaithfulSMul S k] [Nonempty G] :
    FaithfulSMul S (SkewMonoidAlgebra k G) where
  eq_of_smul_eq_smul {_s₁ _s₂} h := by
    apply eq_of_smul_eq_smul fun a : G ->₀ k => congr_arg coeff _
    intro a
    simp_rw [ofCoeff_smul, h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: k] [SMul S₁ S₂] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k]
  body: ⟨fun _ _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, smul_assoc]⟩

中文:
实例 [加法幺半群
  签名: k] [标量乘法 S₁ S₂] [SMulZero类 S₁ k] [SMulZero类 S₂ k]
  定义体: ⟨fun _ _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, smul_assoc]⟩

Depends on / 依赖: ofCoeff_smul, simp_rw, smul_assoc
-/
instance [AddMonoid k] [SMul S₁ S₂] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k]
    [IsScalarTower S₁ S₂ k] : IsScalarTower S₁ S₂ (SkewMonoidAlgebra k G) :=
  ⟨fun _ _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, smul_assoc]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: k] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k] [SMulCommClass S₁ S₂ k] :
  body: ⟨fun _ _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, smul_comm]⟩

中文:
实例 [加法幺半群
  签名: k] [SMulZero类 S₁ k] [SMulZero类 S₂ k] [标量交换类 S₁ S₂ k] :
  定义体: ⟨fun _ _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, smul_comm]⟩

Depends on / 依赖: ofCoeff_smul, simp_rw, smul_comm
-/
instance [AddMonoid k] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k] [SMulCommClass S₁ S₂ k] :
    SMulCommClass S₁ S₂ (SkewMonoidAlgebra k G) :=
  ⟨fun _ _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, smul_comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: k] [SMulZeroClass S k] [SMulZeroClass Sᵐᵒᵖ k] [IsCentralScalar S k] :
  body: ⟨fun _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, op_smul_eq_smul]⟩

中文:
实例 [加法幺半群
  签名: k] [SMulZero类 S k] [SMulZero类 Sᵐᵒᵖ k] [中心标量 S k] :
  定义体: ⟨fun _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, op_smul_eq_smul]⟩

Depends on / 依赖: ofCoeff_smul, op_smul_eq_smul, simp_rw
-/
instance [AddMonoid k] [SMulZeroClass S k] [SMulZeroClass Sᵐᵒᵖ k] [IsCentralScalar S k] :
    IsCentralScalar S (SkewMonoidAlgebra k G) :=
  ⟨fun _ ⟨_⟩ => by simp_rw [← ofCoeff_smul, op_smul_eq_smul]⟩

section Module.Free

variable [Semiring S]

/--
Definition of `coeffLinearEquiv` / `coeffLinearEquiv` 的定义

English:
definition coeffLinearEquiv
  signature: [AddCommMonoid k] [Module S k]
  body: AddEquiv.toLinearEquiv coeffAddEquiv (by simp)

@[deprecated (since := "2026-07-04")] alias toFinsuppLinearEquiv := coeffLinearEquiv

中文:
定义 coeffLinearEquiv
  签名: [加法交换幺半群 k] [模 S k]
  定义体: AddEquiv.toLinearEquiv coeffAddEquiv (by simp)

@[deprecated (since := "2026-07-04")] alias toFinsuppLinearEquiv := coeffLinearEquiv

Depends on / 依赖: AddEquiv, AddEquiv.toLinearEquiv, coeffAddEquiv, toLinearEquiv
-/
def coeffLinearEquiv [AddCommMonoid k] [Module S k] : SkewMonoidAlgebra k G ≃ₗ[S] (G ->₀ k) :=
  AddEquiv.toLinearEquiv coeffAddEquiv (by simp)

@[deprecated (since := "2026-07-04")] alias toFinsuppLinearEquiv := coeffLinearEquiv

/--
Definition of `basisSingleOne` / `basisSingleOne` 的定义

English:
definition basisSingleOne
  signature: [Semiring k]
  body: coeffLinearEquiv

中文:
定义 basisSingleOne
  签名: [半环 k]
  定义体: coeffLinearEquiv

Depends on / 依赖: coeffLinearEquiv
-/
def basisSingleOne [Semiring k] : Module.Basis G k (SkewMonoidAlgebra k G) where
  repr := coeffLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: k] : Module.Free k (SkewMonoidAlgebra k G)
  body: Module.Free.of_basis basisSingleOne

中文:
实例 [半环
  签名: k] : 模.自由 k (斜幺半群代数 k G)
  定义体: Module.Free.of_basis basisSingleOne

Depends on / 依赖: Module, Module.Free.of_basis, basisSingleOne, of_basis
-/
instance [Semiring k] : Module.Free k (SkewMonoidAlgebra k G) :=
  Module.Free.of_basis basisSingleOne

end Module.Free

variable {M α : Type*} [Monoid G] [AddCommMonoid M] [MulAction G α]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the file `MathlibTest/instance_diamonds.lean` for examples of such conflicts. -/
@[instance_reducible]
/--
Definition of `comapSMul` / `comapSMul` 的定义

English:
definition comapSMul
  signature: : SMul G (SkewMonoidAlgebra M α) where smul g
  body: mapDomain (g • ·)

中文:
定义 comapSMul
  签名: : 标量乘法 G (斜幺半群代数 M α) where smul g
  定义体: mapDomain (g • ·)

Depends on / 依赖: mapDomain
-/
def comapSMul : SMul G (SkewMonoidAlgebra M α) where smul g := mapDomain (g • ·)

attribute [local instance] comapSMul

/--
theorem `comapSMul_def` / 定理 `comapSMul_def`

English:
theorem comapSMul_def
  given: (g : G) (f : SkewMonoidAlgebra M α)
  statement: g • f = mapDomain (g • ·) f
  proof: rfl

@[simp]

中文:
定理 comapSMul_def
  条件: (g : G) (f : 斜幺半群代数 M α)
  结论: g • f = mapDomain (g • ·) f
  证明: rfl

@[simp]
-/
theorem comapSMul_def (g : G) (f : SkewMonoidAlgebra M α) : g • f = mapDomain (g • ·) f := rfl

@[simp]
/--
theorem `comapSMul_single` / 定理 `comapSMul_single`

English:
theorem comapSMul_single
  given: (g : G) (a : α) (b : M)
  statement: g • single a b = single (g • a) b
  proof: mapDomain_single

中文:
定理 comapSMul_single
  条件: (g : G) (a : α) (b : M)
  结论: g • single a b = single (g • a) b
  证明: mapDomain_single

Depends on / 依赖: mapDomain_single
-/
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single

/-- `comapSMul` is multiplicative -/
@[instance_reducible]
/--
Definition of `comapMulAction` / `comapMulAction` 的定义

English:
definition comapMulAction
  signature: : MulAction G (SkewMonoidAlgebra M α) where
  body: by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def]; rw [comapSMul_def]; rw [comapSMul_def]; rw [← comp_smul_left]; rw [mapDomain_comp]

中文:
定义 comapMulAction
  签名: : 乘法作用 G (斜幺半群代数 M α) where
  定义体: by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def]; rw [comapSMul_def]; rw [comapSMul_def]; rw [← comp_smul_left]; rw [mapDomain_comp]

Depends on / 依赖: comapSMul_def, comp_smul_left, mapDomain_comp, mapDomain_id, mul_smul, one_smul_eq_id
-/
def comapMulAction : MulAction G (SkewMonoidAlgebra M α) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def]; rw [comapSMul_def]; rw [comapSMul_def]; rw [← comp_smul_left]; rw [mapDomain_comp]

attribute [local instance] comapMulAction
/-- This is not an instance as it conflicts with `SkewMonoidAlgebra.distribMulAction`
  when `G = kˣ`. -/
@[instance_reducible]
/--
Definition of `comapDistribMulActionSelf` / `comapDistribMulActionSelf` 的定义

English:
definition comapDistribMulActionSelf
  signature: [AddCommMonoid k]
  body: by
    ext
    simp [comapSMul_def, mapDomain]
  smul_add g f f' := by
    ext
    simp [comapSMul_def, map_add]

中文:
定义 comapDistribMulActionSelf
  签名: [加法交换幺半群 k]
  定义体: by
    ext
    simp [comapSMul_def, mapDomain]
  smul_add g f f' := by
    ext
    simp [comapSMul_def, map_add]

Depends on / 依赖: comapSMul_def, mapDomain, map_add, smul_add
-/
def comapDistribMulActionSelf [AddCommMonoid k] :
    DistribMulAction G (SkewMonoidAlgebra k G) where
  smul_zero g := by
    ext
    simp [comapSMul_def, mapDomain]
  smul_add g f f' := by
    ext
    simp [comapSMul_def, map_add]

end DerivedInstances

section coeff_mul

variable [Semiring k]

section Mul

variable [Mul G] [SMulZeroClass G k]

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  statement: [DecidableEq G] (f g : SkewMonoidAlgebra k G)
  proof: by
  rw [mul_def]; rw [coeff_sum]; congr; ext
  rw [coeff_sum]; congr; ext
  exact coeff_single_apply

中文:
定理 coeff_mul
  结论: [DecidableEq G] (f g : 斜幺半群代数 k G)
  证明: by
  rw [mul_def]; rw [coeff_sum]; congr; ext
  rw [coeff_sum]; congr; ext
  exact coeff_single_apply

Depends on / 依赖: coeff_single_apply, coeff_sum, mul_def
-/
theorem coeff_mul [DecidableEq G] (f g : SkewMonoidAlgebra k G)
    (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ =>
      if a₁ * a₂ = x then b₁ * a₁ • b₂ else 0 := by
  rw [mul_def]; rw [coeff_sum]; congr; ext
  rw [coeff_sum]; congr; ext
  exact coeff_single_apply

/--
theorem `coeff_mul_antidiagonal_of_finset` / 定理 `coeff_mul_antidiagonal_of_finset`

English:
theorem coeff_mul_antidiagonal_of_finset
  statement: (f g : SkewMonoidAlgebra k G) (x : G)
  proof: by
  classical
  let F : G × G -> k := fun p => if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ in f.support, ∑ a₂ in g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p in f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
    _ = ∑ p in (f.sup

中文:
定理 coeff_mul_antidiagonal_of_finset
  结论: (f g : 斜幺半群代数 k G) (x : G)
  证明: by
  classical
  let F : G × G -> k := fun p => if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ in f.support, ∑ a₂ in g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p in f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
    _ = ∑ p in (f.sup

Depends on / 依赖: Finset, Finset.sum_filter, Finset.sum_product, classical, coeff_mul, f.coeff, f.support, filter, g.coeff, g.support, s.filter, sum_filter, sum_product, support
-/
theorem coeff_mul_antidiagonal_of_finset (f g : SkewMonoidAlgebra k G) (x : G)
    (s : Finset (G × G)) (hs : forall {p : G × G}, p in s ↔ p.1 * p.2 = x) :
    (f * g).coeff x = ∑ p in s, f.coeff p.1 * p.1 • g.coeff p.2 := by
  classical
  let F : G × G -> k := fun p => if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ in f.support, ∑ a₂ in g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p in f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
    _ = ∑ p in (f.support ×ˢ g.support).filter fun p : G × G => p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p in s.filter fun p : G × G => p.1 in f.support ∧ p.2 in g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 :=
      (Finset.sum_congr (by ext; simp [Finset.mem_filter, Finset.mem_product, hs, and_comm])
        fun _ _ => rfl)
    _ = ∑ p in s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp => by
        simp only [Finset.mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all

/--
theorem `coeff_mul_antidiagonal_finsum` / 定理 `coeff_mul_antidiagonal_finsum`

English:
theorem coeff_mul_antidiagonal_finsum
  given: (f g : SkewMonoidAlgebra k G) (x : G)
  proof: by
  have : ({p : G × G | p.1 * p.2 = x}
      inter Function.support fun p => f.coeff p.1 * p.1 • g.coeff p.2).Finite := by
    apply Set.Finite.inter_of_right
    apply Set.Finite.subset (Finset.finite_toSet ((f.support).product (g.support)))
    aesop
  rw [← finsum_mem_inter_support]; rw [finsum

中文:
定理 coeff_mul_antidiagonal_finsum
  条件: (f g : 斜幺半群代数 k G) (x : G)
  证明: by
  have : ({p : G × G | p.1 * p.2 = x}
      inter Function.support fun p => f.coeff p.1 * p.1 • g.coeff p.2).Finite := by
    apply Set.Finite.inter_of_right
    apply Set.Finite.subset (Finset.finite_toSet ((f.support).product (g.support)))
    aesop
  rw [← finsum_mem_inter_support]; rw [finsum

Depends on / 依赖: Finite, Finset, Finset.finite_toSet, Function, Function.support, Set.Finite.inter_of_right, Set.Finite.subset, Set.Finite.toFinset, classical, f.coeff, f.support, finite_toSet, finsum_mem_eq_finite_toFinset_sum, finsum_mem_inter_support, g.coeff, g.support, inter_of_right, product, subset, support
-/
theorem coeff_mul_antidiagonal_finsum (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = ∑ᶠ p in {p : G × G | p.1 * p.2 = x}, f.coeff p.1 * p.1 • g.coeff p.2 := by
  have : ({p : G × G | p.1 * p.2 = x}
      inter Function.support fun p => f.coeff p.1 * p.1 • g.coeff p.2).Finite := by
    apply Set.Finite.inter_of_right
    apply Set.Finite.subset (Finset.finite_toSet ((f.support).product (g.support)))
    aesop
  rw [← finsum_mem_inter_support]; rw [finsum_mem_eq_finite_toFinset_sum _ this]
  classical
  let s := Set.Finite.toFinset (s := ({p : G × G | p.1 * p.2 = x}
    inter Function.support fun p => f.coeff p.1 * p.1 • g.coeff p.2)) this
  let F : G × G -> k := fun p => if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ in f.support, ∑ a₂ in g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p in f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
    _ = ∑ p in (f.support ×ˢ g.support).filter fun p : G × G => p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p in s.filter fun p : G × G => p.1 in f.support ∧ p.2 in g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 := by
        apply Finset.sum_congr_of_eq_on_inter <;> aesop
    _ = ∑ p in s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp => by
        simp only [Finset.mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all

/--
theorem `coeff_mul_single_aux` / 定理 `coeff_mul_single_aux`

English:
theorem coeff_mul_single_aux
  statement: (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
  proof: by
  classical
  have A : forall a₁ b₁, ((single x r).sum fun a₂ b₂ => ite (a₁ * a₂ = z) (b₁ * a₁ • b₂) 0) =
      ite (a₁ * x = z) (b₁ * a₁ • r) 0 :=
fun a₁ b₁ => sum_single_index by simp
  calc
    (f * (single x r)).coeff z =
        sum f fun a b => if a = y then b * y • r else 0 := by simp [coe

中文:
定理 coeff_mul_single_aux
  结论: (f : 斜幺半群代数 k G) {r : k} {x y z : G}
  证明: by
  classical
  have A : forall a₁ b₁, ((single x r).sum fun a₂ b₂ => ite (a₁ * a₂ = z) (b₁ * a₁ • b₂) 0) =
      ite (a₁ * x = z) (b₁ * a₁ • r) 0 :=
fun a₁ b₁ => sum_single_index by simp
  calc
    (f * (single x r)).coeff z =
        sum f fun a b => if a = y then b * y • r else 0 := by simp [coe

Depends on / 依赖: classical, coeff_mul, f.coeff, f.support, f.support.sum_ite_eq, single, split_ifs, sum_ite_eq, sum_single_index, support
-/
theorem coeff_mul_single_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : forall a, a * x = z ↔ a = y) : (f * single x r).coeff z = f.coeff y * y • r := by
  classical
  have A : forall a₁ b₁, ((single x r).sum fun a₂ b₂ => ite (a₁ * a₂ = z) (b₁ * a₁ • b₂) 0) =
      ite (a₁ * x = z) (b₁ * a₁ • r) 0 :=
fun a₁ b₁ => sum_single_index by simp
  calc
    (f * (single x r)).coeff z =
        sum f fun a b => if a = y then b * y • r else 0 := by simp [coeff_mul, A, H, sum_ite_eq']
    _ = if y in f.support then f.coeff y * y • r else 0 := (f.support.sum_ite_eq' _ _)
    _ = f.coeff y * y • r := by
      split_ifs with h <;> simp [support] at h <;> simp [h]

/--
theorem `coeff_mul_single_of_not_exists_mul` / 定理 `coeff_mul_single_of_not_exists_mul`

English:
theorem coeff_mul_single_of_not_exists_mul
  statement: (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
  proof: by
  classical
  simp only [coeff_mul, smul_zero, mul_zero, ite_self, sum_single_index]
  apply Finset.sum_eq_zero
  simp_rw [ite_eq_right_iff]
  rintro _ _ rfl
  exact False.elim (h _ rfl)

中文:
定理 coeff_mul_single_of_not_存在_mul
  结论: (r : k) {g g' : G} (x : 斜幺半群代数 k G)
  证明: by
  classical
  simp only [coeff_mul, smul_zero, mul_zero, ite_self, sum_single_index]
  apply Finset.sum_eq_zero
  simp_rw [ite_eq_right_iff]
  rintro _ _ rfl
  exact False.elim (h _ rfl)

Depends on / 依赖: False.elim, Finset, Finset.sum_eq_zero, classical, coeff_mul, ite_eq_right_iff, ite_self, mul_zero, simp_rw, smul_zero, sum_eq_zero, sum_single_index
-/
theorem coeff_mul_single_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : forall x, ¬g' = x * g) : (x * single g r).coeff g' = 0 := by
  classical
  simp only [coeff_mul, smul_zero, mul_zero, ite_self, sum_single_index]
  apply Finset.sum_eq_zero
  simp_rw [ite_eq_right_iff]
  rintro _ _ rfl
  exact False.elim (h _ rfl)

/--
theorem `coeff_single_mul_aux` / 定理 `coeff_single_mul_aux`

English:
theorem coeff_single_mul_aux
  statement: (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
  proof: by
  classical
  have : (f.sum fun a b => ite (x * a = y) (0 * x • b) 0) = 0 := by simp
  calc
    (single x r * f).coeff y =
        sum f fun a b => ite (x * a = y) (r * x • b) 0 :=
(coeff_mul _ _ _).trans sum_single_index this
    _ = f.sum fun a b => ite (a = z) (r * x • b) 0 := by simp [H]
    

中文:
定理 coeff_single_mul_aux
  结论: (f : 斜幺半群代数 k G) {r : k} {x y z : G}
  证明: by
  classical
  have : (f.sum fun a b => ite (x * a = y) (0 * x • b) 0) = 0 := by simp
  calc
    (single x r * f).coeff y =
        sum f fun a b => ite (x * a = y) (r * x • b) 0 :=
(coeff_mul _ _ _).trans sum_single_index this
    _ = f.sum fun a b => ite (a = z) (r * x • b) 0 := by simp [H]
    

Depends on / 依赖: classical, coeff_mul, f.coeff, f.sum, f.support, f.support.sum_ite_eq, single, split_ifs, sum_ite_eq, sum_single_index, support
-/
theorem coeff_single_mul_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : forall a, x * a = y ↔ a = z) : (single x r * f).coeff y = r * x • f.coeff z := by
  classical
  have : (f.sum fun a b => ite (x * a = y) (0 * x • b) 0) = 0 := by simp
  calc
    (single x r * f).coeff y =
        sum f fun a b => ite (x * a = y) (r * x • b) 0 :=
(coeff_mul _ _ _).trans sum_single_index this
    _ = f.sum fun a b => ite (a = z) (r * x • b) 0 := by simp [H]
    _ = if z in f.support then r * x • f.coeff z else 0 := (f.support.sum_ite_eq' _ _)
    _ = _ := by split_ifs with h <;> simp [support] at h <;> simp [h]

/--
theorem `coeff_single_mul_of_not_exists_mul` / 定理 `coeff_single_mul_of_not_exists_mul`

English:
theorem coeff_single_mul_of_not_exists_mul
  statement: (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
  proof: by
  classical
  rw [coeff_mul]; rw [sum_single_index]
  · apply Finset.sum_eq_zero
    simp_rw [ite_eq_right_iff]
    rintro g'' _hg'' rfl
    exact absurd ⟨_, rfl⟩ h
  · simp

中文:
定理 coeff_single_mul_of_not_存在_mul
  结论: (r : k) {g g' : G} (x : 斜幺半群代数 k G)
  证明: by
  classical
  rw [coeff_mul]; rw [sum_single_index]
  · apply Finset.sum_eq_zero
    simp_rw [ite_eq_right_iff]
    rintro g'' _hg'' rfl
    exact absurd ⟨_, rfl⟩ h
  · simp

Depends on / 依赖: Finset, Finset.sum_eq_zero, absurd, classical, coeff_mul, ite_eq_right_iff, simp_rw, sum_eq_zero, sum_single_index
-/
theorem coeff_single_mul_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ¬exists d, g' = g * d) : (single g r * x).coeff g' = 0 := by
  classical
  rw [coeff_mul]; rw [sum_single_index]
  · apply Finset.sum_eq_zero
    simp_rw [ite_eq_right_iff]
    rintro g'' _hg'' rfl
    exact absurd ⟨_, rfl⟩ h
  · simp

end Mul

section Monoid

variable [Monoid G] [MulSemiringAction G k]

/--
theorem `coeff_mul_single_one` / 定理 `coeff_mul_single_one`

English:
theorem coeff_mul_single_one
  given: (f : SkewMonoidAlgebra k G) (r : k) (x : G)
  proof: f.coeff_mul_single_aux fun a => by rw [mul_one]

中文:
定理 coeff_mul_single_one
  条件: (f : 斜幺半群代数 k G) (r : k) (x : G)
  证明: f.coeff_mul_single_aux fun a => by rw [mul_one]

Depends on / 依赖: coeff_mul_single_aux, f.coeff_mul_single_aux, mul_one
-/
theorem coeff_mul_single_one (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (f * single 1 r).coeff x = f.coeff x * x • r :=
  f.coeff_mul_single_aux fun a => by rw [mul_one]

/--
theorem `coeff_single_one_mul` / 定理 `coeff_single_one_mul`

English:
theorem coeff_single_one_mul
  given: (f : SkewMonoidAlgebra k G) (r : k) (x : G)
  proof: by
  simp [coeff_single_mul_aux, one_smul]

中文:
定理 coeff_single_one_mul
  条件: (f : 斜幺半群代数 k G) (r : k) (x : G)
  证明: by
  simp [coeff_single_mul_aux, one_smul]

Depends on / 依赖: coeff_single_mul_aux, one_smul
-/
theorem coeff_single_one_mul (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (single (1 : G) r * f).coeff x = r * f.coeff x := by
  simp [coeff_single_mul_aux, one_smul]

end Monoid

section Group

-- We now prove some additional statements that hold for group algebras.
variable [Group G] [MulSemiringAction G k]

@[simp]
/--
theorem `coeff_mul_single` / 定理 `coeff_mul_single`

English:
theorem coeff_mul_single
  given: (f : SkewMonoidAlgebra k G) (r : k) (x y : G)
  proof: f.coeff_mul_single_aux fun _a => eq_mul_inv_iff_mul_eq.symm

@[simp]

中文:
定理 coeff_mul_single
  条件: (f : 斜幺半群代数 k G) (r : k) (x y : G)
  证明: f.coeff_mul_single_aux fun _a => eq_mul_inv_iff_mul_eq.symm

@[simp]

Depends on / 依赖: coeff_mul_single_aux, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq.symm, f.coeff_mul_single_aux
-/
theorem coeff_mul_single (f : SkewMonoidAlgebra k G) (r : k) (x y : G) :
    (f * single x r).coeff y = f.coeff (y * x⁻¹) * (y * x⁻¹) • r :=
  f.coeff_mul_single_aux fun _a => eq_mul_inv_iff_mul_eq.symm

@[simp]
/--
theorem `coeff_single_mul` / 定理 `coeff_single_mul`

English:
theorem coeff_single_mul
  given: (r : k) (x : G) (f : SkewMonoidAlgebra k G) (y : G)
  proof: f.coeff_single_mul_aux fun _z => eq_inv_mul_iff_mul_eq.symm

中文:
定理 coeff_single_mul
  条件: (r : k) (x : G) (f : 斜幺半群代数 k G) (y : G)
  证明: f.coeff_single_mul_aux fun _z => eq_inv_mul_iff_mul_eq.symm

Depends on / 依赖: coeff_single_mul_aux, eq_inv_mul_iff_mul_eq, eq_inv_mul_iff_mul_eq.symm, f.coeff_single_mul_aux
-/
theorem coeff_single_mul (r : k) (x : G) (f : SkewMonoidAlgebra k G) (y : G) :
    (single x r * f).coeff y = r * x • f.coeff (x⁻¹ * y) :=
  f.coeff_single_mul_aux fun _z => eq_inv_mul_iff_mul_eq.symm

/--
theorem `coeff_mul_left` / 定理 `coeff_mul_left`

English:
theorem coeff_mul_left
  given: (f g : SkewMonoidAlgebra k G) (x : G)
  proof: calc
    (f * g).coeff x = sum f fun a b => (single a b * g).coeff x := by
      rw [← coeff_sum]; rw [← sum_mul g f]; rw [f.sum_single]
    _ = _ := by simp

中文:
定理 coeff_mul_left
  条件: (f g : 斜幺半群代数 k G) (x : G)
  证明: calc
    (f * g).coeff x = sum f fun a b => (single a b * g).coeff x := by
      rw [← coeff_sum]; rw [← sum_mul g f]; rw [f.sum_single]
    _ = _ := by simp

Depends on / 依赖: coeff_sum, f.sum_single, single, sum_mul, sum_single
-/
theorem coeff_mul_left (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = f.sum fun a b => b * a • g.coeff (a⁻¹ * x) :=
  calc
    (f * g).coeff x = sum f fun a b => (single a b * g).coeff x := by
      rw [← coeff_sum]; rw [← sum_mul g f]; rw [f.sum_single]
    _ = _ := by simp

/--
theorem `coeff_mul_right` / 定理 `coeff_mul_right`

English:
theorem coeff_mul_right
  given: (f g : SkewMonoidAlgebra k G) (x : G)
  proof: calc
    (f * g).coeff x = sum g fun a b => (f * single a b).coeff x := by
      rw [← coeff_sum]; rw [← mul_sum f g]; rw [g.sum_single]
    _ = _ := by simp

中文:
定理 coeff_mul_right
  条件: (f g : 斜幺半群代数 k G) (x : G)
  证明: calc
    (f * g).coeff x = sum g fun a b => (f * single a b).coeff x := by
      rw [← coeff_sum]; rw [← mul_sum f g]; rw [g.sum_single]
    _ = _ := by simp

Depends on / 依赖: coeff_sum, g.sum_single, mul_sum, single, sum_single
-/
theorem coeff_mul_right (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = g.sum fun a b => f.coeff (x * a⁻¹) * (x * a⁻¹) • b :=
  calc
    (f * g).coeff x = sum g fun a b => (f * single a b).coeff x := by
      rw [← coeff_sum]; rw [← mul_sum f g]; rw [g.sum_single]
    _ = _ := by simp

end Group

end coeff_mul

section AddHom

variable [AddCommMonoid k]

/-- `single` as an `AddMonoidHom`.

See `lsingle` for the stronger version as a linear map. -/
@[simps]
/--
Definition of `singleAddHom` / `singleAddHom` 的定义

English:
definition singleAddHom
  signature: (a : G)
  body: single a
  map_zero' := single_zero a
  map_add' _ := single_add a _

@[ext high]

中文:
定义 singleAddHom
  签名: (a : G)
  定义体: single a
  map_zero' := single_zero a
  map_add' _ := single_add a _

@[ext high]

Depends on / 依赖: single
-/
def singleAddHom (a : G) : k ->+ SkewMonoidAlgebra k G where
  toFun := single a
  map_zero' := single_zero a
  map_add' _ := single_add a _

@[ext high]
/--
theorem `addHom_ext'` / 定理 `addHom_ext'`

English:
theorem addHom_ext'
  given: {N : Type*} [AddZeroClass N] ⦃f g
  statement: SkewMonoidAlgebra k G ->+ N⦄
  proof: addHom_ext fun x => DFunLike.congr_fun (H x)

中文:
定理 addHom_ext'
  条件: {N : 类型} [加法零类 N] ⦃f g
  结论: 斜幺半群代数 k G ->+ N⦄
  证明: addHom_ext fun x => DFunLike.congr_fun (H x)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, addHom_ext, congr_fun
-/
theorem addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g : SkewMonoidAlgebra k G ->+ N⦄
    (H : forall x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)

end AddHom

section Semiring

variable [Semiring k]

section singleOneRingHom

variable [Monoid G] [MulSemiringAction G k]

@[simp]
/--
theorem `single_mul_single` / 定理 `single_mul_single`

English:
theorem single_mul_single
  given: {a₁ a₂ : G} {b₁ b₂ : k}
  proof: (sum_single_index (by simp [zero_mul, single_zero, sum_zero])).trans
    (sum_single_index (by simp [smul_zero, mul_zero, single_zero]))

中文:
定理 single_mul_single
  条件: {a₁ a₂ : G} {b₁ b₂ : k}
  证明: (sum_single_index (by simp [zero_mul, single_zero, sum_zero])).trans
    (sum_single_index (by simp [smul_zero, mul_zero, single_zero]))

Depends on / 依赖: mul_zero, single_zero, smul_zero, sum_single_index, sum_zero, zero_mul
-/
theorem single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} :
    (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂) :=
  (sum_single_index (by simp [zero_mul, single_zero, sum_zero])).trans
    (sum_single_index (by simp [smul_zero, mul_zero, single_zero]))

/--
Definition of `singleOneRingHom` / `singleOneRingHom` 的定义

English:
definition singleOneRingHom
  signature: : k ->+* SkewMonoidAlgebra k G where
  body: singleAddHom 1
  map_one' := rfl
  map_mul' x y := by simp [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, singleAddHom_apply,
    single_mul_single, mul_one, one_smul]

中文:
定义 singleOneRingHom
  签名: : k ->+* 斜幺半群代数 k G where
  定义体: singleAddHom 1
  map_one' := rfl
  map_mul' x y := by simp [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, singleAddHom_apply,
    single_mul_single, mul_one, one_smul]

Depends on / 依赖: singleAddHom
-/
def singleOneRingHom : k ->+* SkewMonoidAlgebra k G where
  __ := singleAddHom 1
  map_one' := rfl
  map_mul' x y := by simp [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, singleAddHom_apply,
    single_mul_single, mul_one, one_smul]

/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  statement: {f g : SkewMonoidAlgebra k G ->+* k} (h₁ : forall b, f (single 1 b) = g (single 1 b))
  proof: have {a : G} {b₁ b₂ : k} : (single 1 b₁) * (single a b₂) = single a (b₁ * b₂) := by
    simp [single_mul_single, one_mul, one_smul]
RingHom.coe_addMonoidHom_injective
    addHom_ext fun a b => by rw [← mul_one b, ← this, AddMonoidHom.coe_coe f,
      AddMonoidHom.coe_coe g, f.map_mul, g.map_mul, h₁,

中文:
定理 ringHom_ext
  结论: {f g : 斜幺半群代数 k G ->+* k} (h₁ : 对任意 b, f (single 1 b) = g (single 1 b))
  证明: have {a : G} {b₁ b₂ : k} : (single 1 b₁) * (single a b₂) = single a (b₁ * b₂) := by
    simp [single_mul_single, one_mul, one_smul]
RingHom.coe_addMonoidHom_injective
    addHom_ext fun a b => by rw [← mul_one b, ← this, AddMonoidHom.coe_coe f,
      AddMonoidHom.coe_coe g, f.map_mul, g.map_mul, h₁,

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, RingHom, RingHom.coe_addMonoidHom_injective, addHom_ext, coe_addMonoidHom_injective, coe_coe, f.map_mul, g.map_mul, h_of, map_mul, mul_one, one_mul, one_smul, single, single_mul_single
-/
theorem ringHom_ext {f g : SkewMonoidAlgebra k G ->+* k} (h₁ : forall b, f (single 1 b) = g (single 1 b))
    (h_of : forall a, f (single a 1) = g (single a 1)) : f = g :=
  have {a : G} {b₁ b₂ : k} : (single 1 b₁) * (single a b₂) = single a (b₁ * b₂) := by
    simp [single_mul_single, one_mul, one_smul]
RingHom.coe_addMonoidHom_injective
    addHom_ext fun a b => by rw [← mul_one b, ← this, AddMonoidHom.coe_coe f,
      AddMonoidHom.coe_coe g, f.map_mul, g.map_mul, h₁, h_of]

end singleOneRingHom

section MapDomain

variable {α α₂ β F : Type*} [Semiring β] [Monoid α] [Monoid α₂] [FunLike F α α₂]

/--
theorem `mapDomain_one` / 定理 `mapDomain_one`

English:
theorem mapDomain_one
  given: [MonoidHomClass F α α₂] (f : F)
  proof: by
  simp_rw [one_def, mapDomain_single, map_one]

中文:
定理 mapDomain_one
  条件: [幺半群态射类 F α α₂] (f : F)
  证明: by
  simp_rw [one_def, mapDomain_single, map_one]

Depends on / 依赖: mapDomain_single, map_one, one_def, simp_rw
-/
theorem mapDomain_one [MonoidHomClass F α α₂] (f : F) :
    (mapDomain f (1 : SkewMonoidAlgebra β α) : SkewMonoidAlgebra β α₂) =
      (1 : SkewMonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_one]

/--
theorem `mapDomain_mul` / 定理 `mapDomain_mul`

English:
theorem mapDomain_mul
  statement: [MulSemiringAction α β] [MulSemiringAction α₂ β]
  proof: by
  rw [mul_def]; rw [map_sum]
  have : (sum x fun a b => sum y fun a₂ b₂ => mapDomain (↑f) (single (a * a₂) (b * a • b₂))) =
      sum (mapDomain (↑f) x) fun a₁ b₁ =>
        sum (mapDomain (↑f) y) fun a₂ b₂ => single (a₁ * a₂) (b₁ * a₁ • b₂) := by
    simp_rw [mapDomain_single, map_mul]
    rw [s

中文:
定理 mapDomain_mul
  结论: [MulSemiring作用 α β] [MulSemiring作用 α₂ β]
  证明: by
  rw [mul_def]; rw [map_sum]
  have : (sum x fun a b => sum y fun a₂ b₂ => mapDomain (↑f) (single (a * a₂) (b * a • b₂))) =
      sum (mapDomain (↑f) x) fun a₁ b₁ =>
        sum (mapDomain (↑f) y) fun a₂ b₂ => single (a₁ * a₂) (b₁ * a₁ • b₂) := by
    simp_rw [mapDomain_single, map_mul]
    rw [s

Depends on / 依赖: add_mul, convert, mapDomain, mapDomain_single, map_mul, map_sum, mul_add, mul_def, simp_rw, single, single_add, smul_add, sum_add, sum_mapDomain_index
-/
theorem mapDomain_mul [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MulHomClass F α α₂] {f : F} (x y : SkewMonoidAlgebra β α)
    (hf : forall (a : α) (x : β), a • x = (f a) • x) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  rw [mul_def]; rw [map_sum]
  have : (sum x fun a b => sum y fun a₂ b₂ => mapDomain (↑f) (single (a * a₂) (b * a • b₂))) =
      sum (mapDomain (↑f) x) fun a₁ b₁ =>
        sum (mapDomain (↑f) y) fun a₂ b₂ => single (a₁ * a₂) (b₁ * a₁ • b₂) := by
    simp_rw [mapDomain_single, map_mul]
    rw [sum_mapDomain_index (by simp) (by simp [add_mul]; rw [single_add]; rw [sum_add])]
    congr
    ext a b c
    rw [sum_mapDomain_index (by simp) (by simp [smul_add]; rw [mul_add]; rw [single_add])]
    simp_rw [hf]
  convert! this using 4
  rw [map_sum]

/--
Definition of `mapDomainRingHom` / `mapDomainRingHom` 的定义

English:
definition mapDomainRingHom
  signature: [MulSemiringAction α β] [MulSemiringAction α₂ β]
  body: (mapDomain f : SkewMonoidAlgebra β α ->+ SkewMonoidAlgebra β α₂)
  map_one' := mapDomain_one f
  map_mul' x y := mapDomain_mul x y hf

中文:
定义 mapDomainRingHom
  签名: [MulSemiring作用 α β] [MulSemiring作用 α₂ β]
  定义体: (mapDomain f : SkewMonoidAlgebra β α ->+ SkewMonoidAlgebra β α₂)
  map_one' := mapDomain_one f
  map_mul' x y := mapDomain_mul x y hf

Depends on / 依赖: SkewMonoidAlgebra, mapDomain
-/
def mapDomainRingHom [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MonoidHomClass F α α₂] {f : F} (hf : forall (a : α) (x : β), a • x = (f a) • x) :
    SkewMonoidAlgebra β α ->+* SkewMonoidAlgebra β α₂ where
  __ := (mapDomain f : SkewMonoidAlgebra β α ->+ SkewMonoidAlgebra β α₂)
  map_one' := mapDomain_one f
  map_mul' x y := mapDomain_mul x y hf

end MapDomain

section of

variable (k G)

variable [Monoid G] [MulSemiringAction G k]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : G ->* SkewMonoidAlgebra k G where
  body: single a 1
  map_one' := rfl
  map_mul' a b := by simp

@[simp]

中文:
定义 of
  签名: : G ->* 斜幺半群代数 k G where
  定义体: single a 1
  map_one' := rfl
  map_mul' a b := by simp

@[simp]

Depends on / 依赖: single
-/
def of : G ->* SkewMonoidAlgebra k G where
  toFun a := single a 1
  map_one' := rfl
  map_mul' a b := by simp

@[simp]
/--
lemma `of_apply` / 引理 `of_apply`

English:
lemma of_apply
  given: (a : G)
  statement: (of k G) a = single a 1
  proof: by
  simp [of, MonoidHom.coe_mk, OneHom.coe_mk]

中文:
引理 of_apply
  条件: (a : G)
  结论: (of k G) a = single a 1
  证明: by
  simp [of, MonoidHom.coe_mk, OneHom.coe_mk]

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, coe_mk
-/
lemma of_apply (a : G) : (of k G) a = single a 1 := by
  simp [of, MonoidHom.coe_mk, OneHom.coe_mk]

/--
theorem `smul_of` / 定理 `smul_of`

English:
theorem smul_of
  given: (g : G) (r : k)
  statement: r • of k G g = single g r
  proof: by
  rw [of_apply]; rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 smul_of
  条件: (g : G) (r : k)
  结论: r • of k G g = single g r
  证明: by
  rw [of_apply]; rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: mul_one, of_apply, smul_eq_mul, smul_single
-/
theorem smul_of (g : G) (r : k) : r • of k G g = single g r := by
  rw [of_apply]; rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: [Nontrivial k]
  proof: fun a b h => by
  simp_rw [of_apply, ← coeff_inj] at h
  simpa using (Finsupp.single_eq_single_iff _ _ _ _).mp h

中文:
定理 of_injective
  条件: [非平凡 k]
  证明: fun a b h => by
  simp_rw [of_apply, ← coeff_inj] at h
  simpa using (Finsupp.single_eq_single_iff _ _ _ _).mp h

Depends on / 依赖: Finsupp, Finsupp.single_eq_single_iff, coeff_inj, of_apply, simp_rw, single_eq_single_iff
-/
theorem of_injective [Nontrivial k] :
    Function.Injective (of k G) := fun a b h => by
  simp_rw [of_apply, ← coeff_inj] at h
  simpa using (Finsupp.single_eq_single_iff _ _ _ _).mp h

/-- If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single a 1`
and `single 1 b`, then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `ringHom_ext'` / 定理 `ringHom_ext'`

English:
theorem ringHom_ext'
  statement: {f g : SkewMonoidAlgebra k G ->+* k}
  proof: ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

中文:
定理 ringHom_ext'
  结论: {f g : 斜幺半群代数 k G ->+* k}
  证明: ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, RingHom, RingHom.congr_fun, congr_fun, h_of, ringHom_ext
-/
theorem ringHom_ext' {f g : SkewMonoidAlgebra k G ->+* k}
    (h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom)
    (h_of : (f : SkewMonoidAlgebra k G ->* k).comp (of k G) =
      (g : SkewMonoidAlgebra k G ->* k).comp (of k G)) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

end of

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

/--
theorem `liftNC_smul` / 定理 `liftNC_smul`

English:
theorem liftNC_smul
  statement: [MulOneClass G] {R : Type*} [Semiring R] (f : k ->+* R) (g : G ->* R) (c : k)
  proof: by
  suffices this :
    (liftNC ↑f g).comp (smulAddHom k (SkewMonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC ↑f g) by simpa using congr($this φ)
  refine addHom_ext' fun a => AddMonoidHom.ext fun b => ?_
  simp [smul_single, mul_assoc]

中文:
定理 liftNC_smul
  结论: [MulOne类 G] {R : 类型} [半环 R] (f : k ->+* R) (g : G ->* R) (c : k)
  证明: by
  suffices this :
    (liftNC ↑f g).comp (smulAddHom k (SkewMonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC ↑f g) by simpa using congr($this φ)
  refine addHom_ext' fun a => AddMonoidHom.ext fun b => ?_
  simp [smul_single, mul_assoc]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, AddMonoidHom.mulLeft, SkewMonoidAlgebra, addHom_ext, liftNC, mulLeft, mul_assoc, smulAddHom, smul_single
-/
theorem liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k ->+* R) (g : G ->* R) (c : k)
    (φ : SkewMonoidAlgebra k G) :
    liftNC (f : k ->+ R) g (c • φ) = f c * liftNC (f : k ->+ R) g φ := by
  suffices this :
    (liftNC ↑f g).comp (smulAddHom k (SkewMonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC ↑f g) by simpa using congr($this φ)
  refine addHom_ext' fun a => AddMonoidHom.ext fun b => ?_
  simp [smul_single, mul_assoc]

variable (k G) [Monoid G] [MulSemiringAction G k]

/--
Instance `isScalarTower_self` / 实例 `isScalarTower_self`

English:
instance isScalarTower_self
  signature: [IsScalarTower k k k]
  body: ⟨fun t a b => by
    simp only [smul_eq_mul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [← smul_sum, smul_mul_assoc, ← smul_single,
        zero_mul, imp_true_iff, sum_zero, single_zero]; rfl⟩

中文:
实例 isScalarTower_self
  签名: [标量塔 k k k]
  定义体: ⟨fun t a b => by
    simp only [smul_eq_mul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [← smul_sum, smul_mul_assoc, ← smul_single,
        zero_mul, imp_true_iff, sum_zero, single_zero]; rfl⟩

Depends on / 依赖: Eq.trans, imp_true_iff, single_zero, smul_eq_mul, smul_mul_assoc, smul_single, smul_sum, sum_smul_index, sum_zero, zero_mul
-/
instance isScalarTower_self [IsScalarTower k k k] :
    IsScalarTower k (SkewMonoidAlgebra k G) (SkewMonoidAlgebra k G) :=
  ⟨fun t a b => by
    simp only [smul_eq_mul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [← smul_sum, smul_mul_assoc, ← smul_single,
        zero_mul, imp_true_iff, sum_zero, single_zero]; rfl⟩

end NonUnitalNonAssocAlgebra

end Semiring

section DistribMulActionHom

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]

/-- `single` as a `DistribMulActionSemiHom`.

See also `lsingle` for the version as a linear map. -/
@[simps]
/--
Definition of `DistribMulActionHom.single` / `DistribMulActionHom.single` 的定义

English:
definition DistribMulActionHom.single
  signature: [DistribMulAction R M] {α : Type*} (a : α)
  body: singleAddHom a
  map_smul' k m := by simp [singleAddHom, smul_single, MonoidHom.id_apply]

中文:
定义 分配乘法作用态射.single
  签名: [分配乘法作用 R M] {α : 类型} (a : α)
  定义体: singleAddHom a
  map_smul' k m := by simp [singleAddHom, smul_single, MonoidHom.id_apply]

Depends on / 依赖: singleAddHom
-/
def DistribMulActionHom.single [DistribMulAction R M] {α : Type*} (a : α) :
    M ->+[R] SkewMonoidAlgebra M α where
  __ := singleAddHom a
  map_smul' k m := by simp [singleAddHom, smul_single, MonoidHom.id_apply]

/--
theorem `distribMulActionHom_ext` / 定理 `distribMulActionHom_ext`

English:
theorem distribMulActionHom_ext
  statement: [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
  proof: DistribMulActionHom.toAddMonoidHom_injective addHom_ext h

中文:
定理 distribMulActionHom_ext
  结论: [分配乘法作用 R M] [分配乘法作用 R N] {α : 类型}
  证明: DistribMulActionHom.toAddMonoidHom_injective addHom_ext h

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.toAddMonoidHom_injective, addHom_ext, toAddMonoidHom_injective
-/
theorem distribMulActionHom_ext [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α ->+[R] N}
    (h : forall (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
DistribMulActionHom.toAddMonoidHom_injective addHom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `distribMulActionHom_ext'` / 定理 `distribMulActionHom_ext'`

English:
theorem distribMulActionHom_ext'
  statement: [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
  proof: distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

中文:
定理 distribMulActionHom_ext'
  结论: [分配乘法作用 R M] [分配乘法作用 R N] {α : 类型}
  证明: distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.congr_fun, congr_fun, distribMulActionHom_ext
-/
theorem distribMulActionHom_ext' [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α ->+[R] N}
    (h : forall a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

variable (R) in
/--
Definition of `lsingle` / `lsingle` 的定义

English:
definition lsingle
  signature: {α : Type*} (a : α) [Module R M]
  body: singleAddHom a
  map_smul' _ _ := (smul_single _ _ _).symm

中文:
定义 lsingle
  签名: {α : 类型} (a : α) [模 R M]
  定义体: singleAddHom a
  map_smul' _ _ := (smul_single _ _ _).symm

Depends on / 依赖: singleAddHom
-/
def lsingle {α : Type*} (a : α) [Module R M] : M ->ₗ[R] (SkewMonoidAlgebra M α) where
  __ := singleAddHom a
  map_smul' _ _ := (smul_single _ _ _).symm

/--
lemma `lsingle_apply` / 引理 `lsingle_apply`

English:
lemma lsingle_apply
  given: {α : Type*} (a : α) [Module R M] (m : M)
  proof: rfl

中文:
引理 lsingle_apply
  条件: {α : 类型} (a : α) [模 R M] (m : M)
  证明: rfl
-/
lemma lsingle_apply {α : Type*} (a : α) [Module R M] (m : M) :
  lsingle R a m = single a m := rfl

/--
theorem `lhom_ext` / 定理 `lhom_ext`

English:
theorem lhom_ext
  given: {α : Type*} [Module R M] [Module R N] ⦃φ ψ
  statement: SkewMonoidAlgebra M α ->ₗ[R] N⦄
  proof: LinearMap.toAddMonoidHom_injective addHom_ext h

@[ext high]

中文:
定理 lhom_ext
  条件: {α : 类型} [模 R M] [模 R N] ⦃φ ψ
  结论: 斜幺半群代数 M α ->ₗ[R] N⦄
  证明: LinearMap.toAddMonoidHom_injective addHom_ext h

@[ext high]

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_injective, addHom_ext, toAddMonoidHom_injective
-/
theorem lhom_ext {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α ->ₗ[R] N⦄
    (h : forall a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
LinearMap.toAddMonoidHom_injective addHom_ext h

@[ext high]
/--
theorem `lhom_ext'` / 定理 `lhom_ext'`

English:
theorem lhom_ext'
  given: {α : Type*} [Module R M] [Module R N] ⦃φ ψ
  statement: SkewMonoidAlgebra M α ->ₗ[R] N⦄
  proof: lhom_ext fun a => LinearMap.congr_fun (h a)

中文:
定理 lhom_ext'
  条件: {α : 类型} [模 R M] [模 R N] ⦃φ ψ
  结论: 斜幺半群代数 M α ->ₗ[R] N⦄
  证明: lhom_ext fun a => LinearMap.congr_fun (h a)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lhom_ext
-/
theorem lhom_ext' {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α ->ₗ[R] N⦄
    (h : forall a, φ.comp (lsingle R a) = ψ.comp (lsingle R a)) : φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Monoid G] [Semiring k] [MulSemiringAction G k]
open NonUnitalAlgHom

/--
theorem `nonUnitalAlgHom_ext` / 定理 `nonUnitalAlgHom_ext`

English:
theorem nonUnitalAlgHom_ext
  statement: [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G ->ₙₐ[k] A}
  proof: by
  apply NonUnitalAlgHom.to_distribMulActionHom_injective
  apply distribMulActionHom_ext'
  intro a
  ext
  simp [singleAddHom_apply, h]

中文:
定理 nonUnitalAlgHom_ext
  结论: [分配乘法作用 k A] {φ₁ φ₂ : 斜幺半群代数 k G ->ₙₐ[k] A}
  证明: by
  apply NonUnitalAlgHom.to_distribMulActionHom_injective
  apply distribMulActionHom_ext'
  intro a
  ext
  simp [singleAddHom_apply, h]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.to_distribMulActionHom_injective, distribMulActionHom_ext, singleAddHom_apply, to_distribMulActionHom_injective
-/
theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G ->ₙₐ[k] A}
    (h : forall x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ := by
  apply NonUnitalAlgHom.to_distribMulActionHom_injective
  apply distribMulActionHom_ext'
  intro a
  ext
  simp [singleAddHom_apply, h]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `nonUnitalAlgHom_ext'` / 定理 `nonUnitalAlgHom_ext'`

English:
theorem nonUnitalAlgHom_ext'
  statement: [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G ->ₙₐ[k] A}
  proof: nonUnitalAlgHom_ext DFunLike.congr_fun h

中文:
定理 nonUnitalAlgHom_ext'
  结论: [分配乘法作用 k A] {φ₁ φ₂ : 斜幺半群代数 k G ->ₙₐ[k] A}
  证明: nonUnitalAlgHom_ext DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, nonUnitalAlgHom_ext
-/
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G ->ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (of k G).toMulHom = φ₂.toMulHom.comp (of k G).toMulHom) : φ₁ = φ₂ :=
nonUnitalAlgHom_ext DFunLike.congr_fun h

end DistribMulActionHom

section CommSemiring

variable [Monoid G] [CommSemiring k]
variable {A : Type*} [Semiring A] [Algebra k A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulSemiringAction
  signature: G A]
  body: singleOneRingHom.comp (algebraMap k A)
  smul_def' r a := by ext; simp [Algebra.smul_def, singleOneRingHom, coeff_single_one_mul]
  commutes' r f := by
    ext
    simp only [singleOneRingHom, singleAddHom, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, 

中文:
实例 [MulSemiring作用
  签名: G A]
  定义体: singleOneRingHom.comp (algebraMap k A)
  smul_def' r a := by ext; simp [Algebra.smul_def, singleOneRingHom, coeff_single_one_mul]
  commutes' r f := by
    ext
    simp only [singleOneRingHom, singleAddHom, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, 

Depends on / 依赖: algebraMap, singleOneRingHom, singleOneRingHom.comp
-/
instance [MulSemiringAction G A]
    [SMulCommClass G k A] : Algebra k (SkewMonoidAlgebra A G) where
  algebraMap := singleOneRingHom.comp (algebraMap k A)
  smul_def' r a := by ext; simp [Algebra.smul_def, singleOneRingHom, coeff_single_one_mul]
  commutes' r f := by
    ext
    simp only [singleOneRingHom, singleAddHom, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, coeff_single_one_mul, Algebra.commutes, coeff_mul_single_one,
      smul_algebraMap, RingHom.coe_comp, comp_apply]

@[simp]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  given: [MulSemiringAction G A] [SMulCommClass G k A]
  proof: rfl

中文:
定理 coe_algebraMap
  条件: [MulSemiring作用 G A] [标量交换类 G k A]
  证明: rfl
-/
theorem coe_algebraMap [MulSemiringAction G A] [SMulCommClass G k A] :
    ⇑(algebraMap k (SkewMonoidAlgebra A G)) = single 1 ∘ algebraMap k A :=
  rfl

/--
theorem `single_eq_algebraMap_mul_of` / 定理 `single_eq_algebraMap_mul_of`

English:
theorem single_eq_algebraMap_mul_of
  given: [MulSemiringAction G k] [SMulCommClass G k k] (a : G) (b : k)
  proof: by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

中文:
定理 single_eq_algebraMap_mul_of
  条件: [MulSemiring作用 G k] [标量交换类 G k k] (a : G) (b : k)
  证明: by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

Depends on / 依赖: coe_algebraMap, comp_apply, mul_one, of_apply, one_mul, single_mul_single, smul_one
-/
theorem single_eq_algebraMap_mul_of [MulSemiringAction G k] [SMulCommClass G k k] (a : G) (b : k) :
    single a b = algebraMap k (SkewMonoidAlgebra k G) b * of k G a := by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

/--
theorem `single_algebraMap_eq_algebraMap_mul_of` / 定理 `single_algebraMap_eq_algebraMap_mul_of`

English:
theorem single_algebraMap_eq_algebraMap_mul_of
  statement: (a : G) (b : k) [MulSemiringAction G A]
  proof: by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

中文:
定理 single_algebraMap_eq_algebraMap_mul_of
  结论: (a : G) (b : k) [MulSemiring作用 G A]
  证明: by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

Depends on / 依赖: coe_algebraMap, comp_apply, mul_one, of_apply, one_mul, single_mul_single, smul_one
-/
theorem single_algebraMap_eq_algebraMap_mul_of (a : G) (b : k) [MulSemiringAction G A]
    [SMulCommClass G k A] :
    single a (algebraMap k A b) = algebraMap k (SkewMonoidAlgebra A G) b * of A G a := by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

/- Hypotheses needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [MulSemiringAction G k] [SMulCommClass G k k]

/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  given: ⦃φ₁ φ₂
  statement: AlgHom k (SkewMonoidAlgebra k G) A⦄
  proof: AlgHom.toLinearMap_injective (lhom_ext' fun a => (LinearMap.ext_ring (h a)))

@[ext high]

中文:
定理 algHom_ext
  条件: ⦃φ₁ φ₂
  结论: 代数态射 k (斜幺半群代数 k G) A⦄
  证明: AlgHom.toLinearMap_injective (lhom_ext' fun a => (LinearMap.ext_ring (h a)))

@[ext high]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, LinearMap, LinearMap.ext_ring, ext_ring, lhom_ext, toLinearMap_injective
-/
theorem algHom_ext ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : forall x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
    AlgHom.toLinearMap_injective (lhom_ext' fun a => (LinearMap.ext_ring (h a)))

@[ext high]
/--
theorem `algHom_ext'` / 定理 `algHom_ext'`

English:
theorem algHom_ext'
  given: ⦃φ₁ φ₂
  statement: AlgHom k (SkewMonoidAlgebra k G) A⦄
  proof: algHom_ext DFunLike.congr_fun h

中文:
定理 algHom_ext'
  条件: ⦃φ₁ φ₂
  结论: 代数态射 k (斜幺半群代数 k G) A⦄
  证明: algHom_ext DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, algHom_ext, congr_fun
-/
theorem algHom_ext' ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : (φ₁ : SkewMonoidAlgebra k G ->* A).comp (of k G) =
      (φ₂ : SkewMonoidAlgebra k G ->* A).comp (of k G)) :
φ₁ = φ₂ := algHom_ext DFunLike.congr_fun h

end CommSemiring

end SkewMonoidAlgebra
