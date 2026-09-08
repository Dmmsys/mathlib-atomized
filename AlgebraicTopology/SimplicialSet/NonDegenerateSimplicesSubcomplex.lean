/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

/-!
# The type of nondegenerate simplices not in a subcomplex

In this file, given a subcomplex `A` of a simplicial set `X`,
we introduce the type `A.N` of nondegenerate simplices of `X`
that are not in `A`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The type of nondegenerate simplices which do not belong to
a given subcomplex of a simplicial set. -/
/-
**SSet.Subcomplex.N** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomplex`。
形式化陈述：{X : _root_.SSet} → X.Subcomplex → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of nondegenerate simplices which do not belong to
a given subcomplex of a simplicial set.
-/
structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

namespace N

variable {A}

/-
**SSet.Subcomplex.N.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subcomplex.N`
。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (s : A.N),   ∃ t, ∃ (ht : t.simplex
 ∉ A.obj (Opposite.op { len := t.dim })), s = { toN := t, notMem := ht }
参数：s : A.N；ht : t.simplex ∉ A.obj (Opposite.op { len := t.dim })。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })
-/
lemma mk'_surjective (s : A.N) :
    ∃ (t : X.N) (ht : t.simplex ∉ A.obj _), s = mk' t ht :=
  ⟨s.toN, s.notMem, rfl⟩

/-- Constructor for the type of nondegenerate simplices which
do not belong to a given subcomplex of a simplicial set. -/
@[simps!]
/-
**SSet.Subcomplex.N.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：mk {n : Nat} (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) (hx' : x ∉ A.obj _
) : A.N where simplex
参数：x : X _⦋n⦌；hx : x in X.nonDegenerate n；hx' : x ∉ A.obj _。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht
· 使用引理 `SSet.N.mk'`：mk'_surjective (s : X.N) : exists (t : X.S) (ht : t.simplex 
in X.nonDegenerate _), s = mk' t ht

--- 原说明 ---
Constructor for the type of nondegenerate simplices which
do not belong to a given subcomplex of a simplicial set.
-/
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
    (hx' : x ∉ A.obj _) : A.N where
  simplex := x
  nonDegenerate := hx
  notMem := hx'

/-- A unification hint for the dimension of `Subcomplex.N.mk`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (n : ℕ) (x : X _⦋n⦌)
    (hx : x ∈ X.nonDegenerate n) (hx' : x ∉ A.obj _) where
  ⊢ (mk x hx hx').dim ≟ n

/-
**SSet.Subcomplex.N.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：mk_surjective (s : A.N) : exists (n : Nat) (x : X _⦋n⦌) (hx : x in X.nonDe
generate n) (hx' : x ∉ A.obj _), s = mk x hx hx'
参数：s : A.N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })
-/
lemma mk_surjective (s : A.N) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
      (hx' : x ∉ A.obj _), s = mk x hx hx' :=
  ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩
/-
**SSet.Subcomplex.N.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：ext_iff (x y : A.N) : x = y ↔ x.toN = y.toN
参数：x y : A.N。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ext_iff (x y : A.N) :
    x = y ↔ x.toN = y.toN := by
  grind [cases SSet.Subcomplex.N]

variable (A) in
@[elab_as_elim]
/-
**SSet.Subcomplex.N.cases** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：cases {motive : X.N -> Prop} (mem : forall (s : X.N), s.subcomplex <= A ->
 motive s) (notMem : forall (s : A.N), motive s.toN) (s : X.N) : motive s
参数：mem : forall (s : X.N), s.subcomplex <= A -> motive s；notMem : forall (s : A.
N), motive s.toN；s : X.N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma cases {motive : X.N → Prop}
    (mem : ∀ (s : X.N), s.subcomplex ≤ A → motive s)
    (notMem : ∀ (s : A.N), motive s.toN)
    (s : X.N) :
    motive s := by
  by_cases hs : s.subcomplex ≤ A
  · exact mem s hs
  · exact notMem (.mk' s (by simpa using hs))
/-
**SSet.Subcomplex.N.eq_iff_sMk_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：eq_iff_sMk_eq {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N) : x = y ↔ S.mk
 x.simplex = S.mk y.simplex
参数：x y : A.N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.N.ext_iff`：ext_iff (x y : A.N) : x = y ↔ x.toN = y.toN
· 使用引理 `SSet.N.ext_iff`：ext_iff (x y : X.N) : x = y ↔ x.toS = y.toS
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_iff_sMk_eq {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N) :
    x = y ↔ S.mk x.simplex = S.mk y.simplex := by
  rw [N.ext_iff, SSet.N.ext_iff]
/-
**SSet.Subcomplex.N.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.N`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder A.N :=
  PartialOrder.lift toN (fun _ _ ↦ by simp [ext_iff])
/-
**SSet.Subcomplex.N.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：le_iff {x y : A.N} : x <= y ↔ x.toN <= y.toN
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff {x y : A.N} : x ≤ y ↔ x.toN ≤ y.toN :=
  Iff.rfl
/-
**SSet.Subcomplex.N.lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：lt_iff {x y : A.N} : x < y ↔ x.toN < y.toN
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_iff {x y : A.N} : x < y ↔ x.toN < y.toN :=
  Iff.rfl

section

variable (s : A.N) {d : ℕ} (hd : s.dim = d)

/-- When `A` is a subcomplex of a simplicial set `X`,
and `s : A.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
/-
**SSet.Subcomplex.N.cast** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：cast : A.N where toN
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht

--- 原说明 ---
When `A` is a subcomplex of a simplicial set `X`,
and `s : A.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`.
-/
abbrev cast : A.N where
  toN := s.toN.cast hd
  notMem := hd ▸ s.notMem
/-
**SSet.Subcomplex.N.cast_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：cast_eq_self : s.cast hd = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

/-- A unification hint for the dimension of `Subcomplex.N.cast`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (s : A.N) (d : ℕ)
    (hd : s.dim = d) where
  ⊢ (s.cast hd).dim ≟ d

/-- The bijection `A.op.N ≃ A.N` for a subcomplex `A` of a simplicial set.. -/
@[simps -isSimp apply symm_apply]
/-
**SSet.Subcomplex.N.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：opEquiv : A.op.N ≃o A.N where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })

--- 原说明 ---
The bijection `A.op.N ≃ A.N` for a subcomplex `A` of a simplicial set..
-/
def opEquiv : A.op.N ≃o A.N where
  toFun x := N.mk' (SSet.N.opEquiv x.toN) x.notMem
  invFun y := N.mk' (SSet.N.opEquiv.symm y.toN) y.notMem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := SSet.N.opEquiv.map_rel_iff

/-- The bijection `A.N ≃ B.N` on nondegenerate simplices not belonging
to a certain subcomplex that is induced by an isomorphism `X ≅ Y` of
simplicial sets which maps `A : X.Subcomplex` to `B : Y.Subcomplex`. -/
@[simps -isSimp apply symm_apply]
/-
**SSet.Subcomplex.N.orderIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.N`。
形式化陈述：orderIsoOfIso {Y : SSet.{u}} {B : Y.Subcomplex} (e : X ≅ Y) (hA : B.preima
ge e.hom = A) : A.N ≃o B.N where toFun x
参数：e : X ≅ Y；hA : B.preimage e.hom = A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht

--- 原说明 ---
The bijection `A.N ≃ B.N` on nondegenerate simplices not belonging
to a certain subcomplex that is induced by an isomorphism `X ≅ Y` of
simplicial sets which maps `A : X.Subcomplex` to `B : Y.Subcomplex`.
-/
def orderIsoOfIso {Y : SSet.{u}} {B : Y.Subcomplex} (e : X ≅ Y)
    (hA : B.preimage e.hom = A) : A.N ≃o B.N where
  toFun x := N.mk' (SSet.N.orderIsoOfIso e x.toN) (by subst hA; exact x.notMem)
  invFun y := N.mk' ((SSet.N.orderIsoOfIso e).symm y.toN) (by
    obtain rfl : A.preimage e.inv = B := by aesop
    exact y.notMem)
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' {_ _} := (SSet.N.orderIsoOfIso e).map_rel_iff'

end N

/-
**SSet.Subcomplex.existsN** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：existsN {X : SSet.{u}} {n : Nat} (s : X _⦋n⦌) {A : X.Subcomplex} (hs : s ∉
 A.obj _) : exists (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi f ∧ X.map f.op x.simplex =
 s
参数：s : X _⦋n⦌；hs : s ∉ A.obj _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.N.mk'`：mk'_surjective (s : A.N) : exists (t : X.N) (ht :
 t.simplex ∉ A.obj _), s = mk' t ht
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.subcomplex_toN`：subcomplex_toN (x : X.S) : x.toN.subcomplex = x.s
ubcomplex
· 使用定理 `SSet.S.instEpiSimplexCategoryToNπ`：∀ {X : _root_.SSet} (x : X.S), Catego
ryTheory.Epi x.toNπ
· 使用引理 `SSet.S.map_toNπ_op_apply`：map_toNπ_op_apply (x : X.S) : X.map x.toNπ.op 
x.toN.simplex = x.simplex
-/
lemma existsN {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) {A : X.Subcomplex}
    (hs : s ∉ A.obj _) :
    ∃ (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi f ∧ X.map f.op x.simplex = s := by
  refine ⟨⟨(S.mk s).toN, fun h ↦ hs ?_⟩, ⟨(S.mk s).toNπ, inferInstance, S.map_toNπ_op_apply _⟩⟩
  simp only [← ofSimplex_le_iff] at h ⊢
  simpa using h

end SSet.Subcomplex

