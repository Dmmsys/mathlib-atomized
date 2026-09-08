/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

/-!
# Helper structure in order to construct pairings

In this file, we introduce a helper structure `Subcomplex.PairingCore`
in order to construct a pairing for a subcomplex of a simplicial set.
The main difference with `Subcomplex.Pairing` are that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (II) and (I) simplices in such a way that, *definitionally*,
their dimensions are respectively `dim s` or `dim s + 1` for `s : ι`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- A helper structure in order to construct a pairing for a subcomplex of a
simplicial set `X`. The main difference with `Pairing` is that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (I) simplices as `simplex s : X _⦋dim s + 1⦌` for `s : ι`,
and type (II) simplices as a face of `simplex s` in `X _⦋dim s⦌`. -/
/-
**SSet.Subcomplex.PairingCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomplex`。
形式化陈述：{X : _root_.SSet} → X.Subcomplex → Type (max u (v + 1))
参数：max u (v + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper structure in order to construct a pairing for a subcomplex of a
simplicial set `X`. The main difference with `Pairing` is that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (I) simplices as `simplex s : X _⦋dim s + 1⦌` for `s : ι`,
and type (II) simplices as a face of `simplex s` in `X _⦋dim s⦌`.
-/
structure PairingCore where
  /-- the index type -/
  ι : Type v
  /-- the dimension of each type (II) simplex -/
  dim (s : ι) : ℕ
  /-- the family of type (I) simplices -/
  simplex (s : ι) : X _⦋dim s + 1⦌
  /-- the corresponding type (II) simplex is the `1`-codimensional
    face given by this index -/
  index (s : ι) : Fin (dim s + 2)
  nonDegenerate₁ (s : ι) : simplex s ∈ X.nonDegenerate _
  nonDegenerate₂ (s : ι) : X.δ (index s) (simplex s) ∈ X.nonDegenerate _
  notMem₁ (s : ι) : simplex s ∉ A.obj _
  notMem₂ (s : ι) : X.δ (index s) (simplex s) ∉ A.obj _
  injective_type₁' {s t : ι} (h : S.mk (simplex s) = S.mk (simplex t)) : s = t
  injective_type₂' {s t : ι}
    (h : S.mk (X.δ (index s) (simplex s)) = S.mk (X.δ (index t) (simplex t))) : s = t
  type₁_ne_type₂' (s t : ι) : S.mk (simplex s) ≠ S.mk (X.δ (index t) (simplex t))
  surjective' (x : A.N) :
    ∃ (s : ι), x.toS = S.mk (simplex s) ∨ x.toS = S.mk (X.δ (index s) (simplex s))

variable {A}

/-- The `PairingCore` structure induced by a pairing. The opposite construction
is `PairingCore.pairing`. -/
/-
**SSet.Subcomplex.Pairing.pairingCore** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex
.Pairing`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → (P : A.Pairing) → [P.IsProper] → 
A.PairingCore
参数：P : A.Pairing。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS

--- 原说明 ---
The `PairingCore` structure induced by a pairing. The opposite construction
is `PairingCore.pairing`.
-/
noncomputable def Pairing.pairingCore (P : A.Pairing) [P.IsProper] :
    A.PairingCore where
  ι := P.II
  dim s := s.val.dim
  simplex s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).simplex
  index s := (P.isUniquelyCodimOneFace s).index rfl
  nonDegenerate₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).nonDegenerate
  nonDegenerate₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.nonDegenerate
  notMem₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).notMem
  notMem₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.notMem
  injective_type₁' {s t} _ := by
    apply P.p.injective
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff,
      ← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      ← (P.p t).val.cast_eq_self (P.isUniquelyCodimOneFace t).dim_eq]
  injective_type₂' {s t} h := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl,
      (P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff]
  type₁_ne_type₂' s t h := (P.ne (P.p s) t) (by
    rw [(P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      N.ext_iff, SSet.N.ext_iff])
  surjective' x := by
    obtain ⟨s, rfl | rfl⟩ := P.exists_or x
    · refine ⟨s, Or.inr ?_⟩
      simp [(P.isUniquelyCodimOneFace s).δ_index]
    · refine ⟨s, Or.inl ?_⟩
      nth_rw 1 [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq]
      rfl

namespace PairingCore

variable (h : A.PairingCore)

/-- The type (I) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`. -/
@[simps!]
/-
**SSet.Subcomplex.PairingCore.type** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pa
iringCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (I) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`.
-/
def type₁ (s : h.ι) : A.N :=
  Subcomplex.N.mk (h.simplex s) (h.nonDegenerate₁ s) (h.notMem₁ s)

/-- The type (II) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`. -/
@[simps!]
/-
**SSet.Subcomplex.PairingCore.type** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pa
iringCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (II) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`.
-/
def type₂ (s : h.ι) : A.N :=
  Subcomplex.N.mk (X.δ (h.index s) (h.simplex s)) (h.nonDegenerate₂ s)
    (h.notMem₂ s)
/-
**SSet.Subcomplex.PairingCore.injective_type** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.PairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma injective_type₁ : Function.Injective h.type₁ :=
  fun _ _ hst ↦ h.injective_type₁' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)
/-
**SSet.Subcomplex.PairingCore.injective_type** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Sub
complex.PairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma injective_type₂ : Function.Injective h.type₂ :=
  fun s t hst ↦ h.injective_type₂' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)
/-
**SSet.Subcomplex.PairingCore.type** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pa
iringCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma type₁_ne_type₂ (s t : h.ι) : h.type₁ s ≠ h.type₂ t := by
  simpa only [ne_eq, N.ext_iff, SSet.N.ext_iff] using! h.type₁_ne_type₂' s t
/-
**SSet.Subcomplex.PairingCore.surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomp
lex.PairingCore`。
形式化陈述：surjective (x : A.N) : exists (s : h.ι), x = h.type₁ s ∨ x = h.type₂ s
参数：x : A.N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.PairingCore.surjective'`：∀ {X : _root_.SSet} {A : X.Subc
omplex} (self : A.PairingCore) (x : A.N),   ∃ s,     x.toS = { dim := self.dim s
 + 1, simplex := self.simplex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.N.ext_iff`：ext_iff (x y : A.N) : x = y ↔ x.toN = y.toN
· 使用引理 `SSet.N.ext_iff`：ext_iff (x y : X.N) : x = y ↔ x.toS = y.toS
-/
lemma surjective (x : A.N) :
    ∃ (s : h.ι), x = h.type₁ s ∨ x = h.type₂ s := by
  obtain ⟨s, _ | _⟩ := h.surjective' x
  · exact ⟨s, Or.inl (by rwa [N.ext_iff, SSet.N.ext_iff])⟩
  · exact ⟨s, Or.inr (by rwa [N.ext_iff, SSet.N.ext_iff])⟩

/-- The type (I) simplices of `h : A.PairingCore`, as a subset of `A.N`. -/
/-
**SSet.Subcomplex.PairingCore.I** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pairi
ngCore`。
形式化陈述：I : Set A.N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (I) simplices of `h : A.PairingCore`, as a subset of `A.N`.
-/
def I : Set A.N := Set.range h.type₁

/-- The type (II) simplices of `h : A.PairingCore`, as a subset of `A.N`. -/
/-
**SSet.Subcomplex.PairingCore.II** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pair
ingCore`。
形式化陈述：II : Set A.N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (II) simplices of `h : A.PairingCore`, as a subset of `A.N`.
-/
def II : Set A.N := Set.range h.type₂

/-- The bijection `h.ι ≃ h.I` when `h : A.PairingCore`. -/
@[simps! apply_coe]
/-
**SSet.Subcomplex.PairingCore.equivI** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.
PairingCore`。
形式化陈述：equivI : h.ι ≃ h.I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.PairingCore.injective_type₁`：injective_type₁ : Function.
Injective h.type₁

--- 原说明 ---
The bijection `h.ι ≃ h.I` when `h : A.PairingCore`.
-/
noncomputable def equivI : h.ι ≃ h.I := Equiv.ofInjective _ h.injective_type₁

/-- The bijection `h.ι ≃ h.II` when `h : A.PairingCore`. -/
@[simps! apply_coe]
/-
**SSet.Subcomplex.PairingCore.equivII** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex
.PairingCore`。
形式化陈述：equivII : h.ι ≃ h.II
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.PairingCore.injective_type₂`：injective_type₂ : Function.
Injective h.type₂

--- 原说明 ---
The bijection `h.ι ≃ h.II` when `h : A.PairingCore`.
-/
noncomputable def equivII : h.ι ≃ h.II := Equiv.ofInjective _ h.injective_type₂

/-- The pairing induced by `h : A.PairingCore`. -/
@[simps I II]
/-
**SSet.Subcomplex.PairingCore.pairing** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex
.PairingCore`。
形式化陈述：pairing : A.Pairing where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The pairing induced by `h : A.PairingCore`.
-/
noncomputable def pairing : A.Pairing where
  I := h.I
  II := h.II
  inter := by
    ext s
    simp only [I, II, Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, forall_exists_index]
    rintro t rfl s
    exact (h.type₁_ne_type₂ t s).symm
  union := by
    ext s
    have := h.surjective s
    simp only [I, II, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    aesop
  p := h.equivII.symm.trans h.equivI

@[simp]
/-
**SSet.Subcomplex.PairingCore.pairing_p_equivII** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
Subcomplex.PairingCore`。
形式化陈述：pairing_p_equivII (x : h.ι) : DFunLike.coe (F
参数：x : h.ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_p_equivII (x : h.ι) :
    DFunLike.coe (F := h.II ≃ h.I) h.pairing.p (h.equivII x) = h.equivI x := by
  simp [pairing]

@[simp]
/-
**SSet.Subcomplex.PairingCore.pairing_p_symm_equivI** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.Subcomplex.PairingCore`。
形式化陈述：pairing_p_symm_equivI (x : h.ι) : DFunLike.coe (F
参数：x : h.ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_p_symm_equivI (x : h.ι) :
    DFunLike.coe (F := h.I ≃ h.II) h.pairing.p.symm (h.equivI x) = h.equivII x := by
  simp [pairing]

set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.PairingCore.type** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pa
iringCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma type₁_pairing (x : h.ι) :
    h.type₁ x = h.pairing.p (h.equivII x) := by
  simp +instances

/-- The condition that `h : A.PairingCore` is proper, i.e. for each `s : h.ι`,
the type (II) simplex `h.type₂ s` is uniquely a `1`-codimensional
face of the type (I) simplex `h.type₁ s`. -/
/-
**SSet.Subcomplex.PairingCore.IsProper** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomp
lex.PairingCore`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.PairingCore → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that `h : A.PairingCore` is proper, i.e. for each `s : h.ι`,
the type (II) simplex `h.type₂ s` is uniquely a `1`-codimensional
face of the type (I) simplex `h.type₁ s`.
-/
class IsProper : Prop where
  isUniquelyCodimOneFace (s : h.ι) :
    S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS
/-
**SSet.Subcomplex.PairingCore.isUniquelyCodimOneFace** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.PairingCore`。
形式化陈述：isUniquelyCodimOneFace [h.IsProper] (s : h.ι) : S.IsUniquelyCodimOneFace (
h.type₂ s).toS (h.type₁ s).toS
参数：s : h.ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.PairingCore.IsProper.isUniquelyCodimOneFace`：∀ {X : _roo
t_.SSet} {A : X.Subcomplex} {h : A.PairingCore} [self : h.IsProper] (s : h.ι),  
 (h.type₂ s).IsUniquelyCodimOneFace (h.type₁ s).t…
-/
lemma isUniquelyCodimOneFace [h.IsProper] (s : h.ι) :
    S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS :=
  IsProper.isUniquelyCodimOneFace _
/-
**SSet.Subcomplex.PairingCore.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairin
gCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Nonsingular] : h.IsProper where
  isUniquelyCodimOneFace s :=
    (S.IsUniquelyCodimOneFace.iff _ _).2
      (existsUnique_of_exists_of_unique ⟨_, rfl⟩
        (fun _ _ hi hj ↦ Nonsingular.δ_injective _
          (h.nonDegenerate₁ s) _ _ (hi.trans hj.symm)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.PairingCore.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairin
gCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h.IsProper] : h.pairing.IsProper where
  isUniquelyCodimOneFace x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    simpa using h.isUniquelyCodimOneFace s
/-
**SSet.Subcomplex.PairingCore.isProper_pairing_iff** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.Subcomplex.PairingCore`。
形式化陈述：isProper_pairing_iff : h.pairing.IsProper ↔ h.IsProper
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.PairingCore.type₁_pairing`：type₁_pairing (x : h.ι) : h.t
ype₁ x = h.pairing.p (h.equivII x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.PairingCore.equivII_apply_coe`：∀ {X : _root_.SSet} {A : 
X.Subcomplex} (h : A.PairingCore) (a : h.ι), ↑(h.equivII a) = h.type₂ a
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
· 使用定理 `SSet.Subcomplex.PairingCore.instIsProperPairingOfIsProper`：∀ {X : _root_
.SSet} {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper], h.pairing.IsProper
-/
lemma isProper_pairing_iff :
    h.pairing.IsProper ↔ h.IsProper := by
  refine ⟨fun _ ↦ ⟨fun s ↦ ?_⟩, fun _ ↦ inferInstance⟩
  simpa [type₁_pairing] using h.pairing.isUniquelyCodimOneFace (h.equivII s)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SSet.Subcomplex.PairingCore.isUniquelyCodimOneFace_index** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.Subcomplex.PairingCore`。
形式化陈述：isUniquelyCodimOneFace_index [h.IsProper] (s : h.ι) : (h.isUniquelyCodimOn
eFace s).index rfl = h.index s
参数：s : h.ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.PairingCore.isUniquelyCodimOneFace`：isUniquelyCodimOneFa
ce [h.IsProper] (s : h.ι) : S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s)
.toS
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.δ_eq_iff`：δ_eq_iff (i : Fin (d + 2)) : X.δ
 i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔ i = hxy.ind
ex hd
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Subcomplex.PairingCore.type₁_simplex`：∀ {X : _root_.SSet} {A : X.Su
bcomplex} (h : A.PairingCore) (s : h.ι), (h.type₁ s).simplex = h.simplex s
· 使用定理 `SSet.Subcomplex.PairingCore.type₂_simplex`：∀ {X : _root_.SSet} {A : X.Su
bcomplex} (h : A.PairingCore) (s : h.ι),   (h.type₂ s).simplex =     (CategoryTh
eory.ConcreteCategory.hom (Cate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isUniquelyCodimOneFace_index [h.IsProper] (s : h.ι) :
    (h.isUniquelyCodimOneFace s).index rfl = h.index s := by
  symm
  simp [← (h.isUniquelyCodimOneFace s).δ_eq_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.PairingCore.isUniquelyCodimOneFace_index_coe** 是 Mathlib 中的一个引
理，位于命名空间 `SSet.Subcomplex.PairingCore`。
形式化陈述：isUniquelyCodimOneFace_index_coe [h.IsProper] (s : h.ι) {d : Nat} (hd : h.
dim s = d) : ((h.isUniquelyCodimOneFace s).index hd).val = (h.index s).val
参数：s : h.ι；hd : h.dim s = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.PairingCore.isUniquelyCodimOneFace`：isUniquelyCodimOneFa
ce [h.IsProper] (s : h.ι) : S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s)
.toS
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.PairingCore.isUniquelyCodimOneFace_index`：isUniquelyCodi
mOneFace_index [h.IsProper] (s : h.ι) : (h.isUniquelyCodimOneFace s).index rfl =
 h.index s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isUniquelyCodimOneFace_index_coe
    [h.IsProper] (s : h.ι) {d : ℕ} (hd : h.dim s = d) :
    ((h.isUniquelyCodimOneFace s).index hd).val = (h.index s).val := by
  subst hd
  simp

/-- The condition that `h : A.PairingCore` involves only inner horns. -/
/-
**SSet.Subcomplex.PairingCore.IsInner** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcompl
ex.PairingCore`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.PairingCore → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that `h : A.PairingCore` involves only inner horns.
-/
class IsInner where
  ne_zero (s : h.ι) : h.index s ≠ 0
  ne_last (s : h.ι) : h.index s ≠ Fin.last _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.PairingCore.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairin
gCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h.IsInner] [h.IsProper] : h.pairing.IsInner where
  ne_zero x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_zero s
  ne_last x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_last s

/-- The ancestrality relation on the index type of `h : A.PairingCore`. -/
/-
**SSet.Subcomplex.PairingCore.AncestralRel** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subco
mplex.PairingCore`。
形式化陈述：AncestralRel (s t : h.ι) : Prop
参数：s t : h.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ancestrality relation on the index type of `h : A.PairingCore`.
-/
def AncestralRel (s t : h.ι) : Prop :=
  s ≠ t ∧ h.type₂ s < h.type₁ t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.PairingCore.ancestralRel_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S
ubcomplex.PairingCore`。
形式化陈述：ancestralRel_iff (s t : h.ι) : h.AncestralRel s t ↔ h.pairing.AncestralRel
 (h.equivII s) (h.equivII t)
参数：s t : h.ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `SSet.Subcomplex.PairingCore.pairing_p_equivII`：pairing_p_equivII (x : h.
ι) : DFunLike.coe (F
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ancestralRel_iff (s t : h.ι) :
    h.AncestralRel s t ↔ h.pairing.AncestralRel (h.equivII s) (h.equivII t) := by
  simp [AncestralRel, Pairing.AncestralRel]

/-- When the ancestrality relation is well founded, we say that `h : A.PairingCore`
is regular. -/
/-
**SSet.Subcomplex.PairingCore.IsRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcom
plex.PairingCore`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.PairingCore → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the ancestrality relation is well founded, we say that `h : A.PairingCore`
is regular.
-/
class IsRegular (h : A.PairingCore) extends h.IsProper where
  wf (h) : WellFounded h.AncestralRel

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Subcomplex.PairingCore.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairin
gCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h.IsRegular] : h.pairing.IsRegular where
  wf := by
    have := IsRegular.wf h
    rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
    exact ⟨fun ⟨f, hf⟩ ↦ this.false
      ⟨fun n ↦ h.equivII.symm (f n), fun n ↦ by simpa [ancestralRel_iff] using hf n⟩⟩
/-
**SSet.Subcomplex.PairingCore.isRegular_pairing_iff** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.Subcomplex.PairingCore`。
形式化陈述：isRegular_pairing_iff (h : A.PairingCore) : h.pairing.IsRegular ↔ h.IsRegu
lar
参数：h : A.PairingCore。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.PairingCore.isProper_pairing_iff`：isProper_pairing_iff :
 h.pairing.IsProper ↔ h.IsProper
· 使用定理 `SSet.Subcomplex.Pairing.IsRegular.toIsProper`：∀ {X : _root_.SSet} {A : X
.Subcomplex} {P : A.Pairing} [self : P.IsRegular], P.IsProper
· 使用引理 `SSet.Subcomplex.Pairing.wf`：wf : WellFounded P.AncestralRel
· 使用定理 `wellFounded_iff_isEmpty_descending_chain`：wellFounded_iff_isEmpty_descen
ding_chain {α} {r : α -> α -> Prop} : WellFounded r ↔ IsEmpty { f : Nat -> α // 
forall n, r (f (n + 1)) (f n) …
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `SSet.Subcomplex.PairingCore.instIsRegularPairingOfIsRegular`：∀ {X : _roo
t_.SSet} {A : X.Subcomplex} (h : A.PairingCore) [h.IsRegular], h.pairing.IsRegul
ar
-/
lemma isRegular_pairing_iff (h : A.PairingCore) :
    h.pairing.IsRegular ↔ h.IsRegular := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : h.IsProper := by
    rw [← isProper_pairing_iff]
    infer_instance
  constructor
  have := h.pairing.wf
  rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
  exact ⟨fun ⟨f, hf⟩ ↦ this.false
    ⟨fun n ↦ h.equivII (f n), fun n ↦ by simpa [ancestralRel_iff] using hf n⟩⟩

end PairingCore

end SSet.Subcomplex

