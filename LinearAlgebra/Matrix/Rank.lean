/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `Matrix.rank_eq_finrank_range_toLin`.

## Main declarations

* `Matrix.rank`: the rank of a matrix
* `Matrix.cRank`: the rank of a matrix as a cardinal
* `Matrix.eRank`: the rank of a matrix as a term in `ℕ∞`.

## Main results

* `Matrix.rank_eq_finrank_range_toLin`: the rank equals the dimension of the range of the
corresponding linear map, and is therefore independent of the choice of bases.
* `Matrix.rank_eq_finrank_span_cols`, `Matrix.rank_eq_finrank_span_row`: the rank equals the
dimension of the space spanned by the columns (resp. rows).
* `Matrix.rank_transpose`: transposing a matrix does not change its rank.
* `Matrix.rank_mul_le`: the rank of `A * B` is at most the rank of `A` and at most the rank of `B`.
* `Matrix.rank_mul_eq_left_of_isUnit_det`, `Matrix.rank_mul_eq_right_of_isUnit_det`: multiplying by
an invertible matrix does not change the rank.
* `Matrix.exists_rank_normal_form`: every square matrix over a field can be brought, by left and
right multiplication by invertible matrices, into the block form `fromBlocks 1 0 0 0`, where the
identity block has size equal to the rank of the matrix.
-/

@[expose] public section

open Matrix

namespace Matrix

open Module Cardinal Set Submodule

universe ul um um₀ un un₀ uo uR
variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}
variable {R : Type uR}

section Infinite

variable [Semiring R]

/-- The rank of a matrix, defined as the dimension of its column space, as a cardinal. -/
/-
**Matrix.cRank** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：cRank (A : Matrix m n R) : Cardinal
参数：A : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a matrix, defined as the dimension of its column space, as a cardina
l.
-/
noncomputable def cRank (A : Matrix m n R) : Cardinal := Module.rank R <| span R <| range A.col

@[simp]
/-
**Matrix.cRank_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.cRank = 1
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
-/
theorem cRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.cRank = 1 :=
  rank_subsingleton _ _
/-
**Matrix.cRank_toNat_eq_finrank** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cRank_toNat_eq_finrank (A : Matrix m n R) : A.cRank.toNat = Module.finrank
 R (span R (range A.col))
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cRank_toNat_eq_finrank (A : Matrix m n R) :
    A.cRank.toNat = Module.finrank R (span R (range A.col)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.lift_cRank_submatrix_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：lift_cRank_submatrix_le (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n) : l
ift.{um} (A.submatrix r c).cRank <= lift.{um₀} A.cRank
参数：A : Matrix m n R；r : m₀ -> m；c : n₀ -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.lift_monotone`：lift_monotone : Monotone lift
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_span`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ 
: Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Matrix.cRank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : S
emiring R] (A : Matrix m n R),   A.cRank = Module.rank R ↥(Submodule.span R (Set
.range …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lift_rank_map_le`：lift_rank_map_le (f : M ->ₗ[R] M') (p : Submodule R M)
 : Cardinal.lift.{v} (Module.rank R (p.map f)) <= Cardinal.lift.{v'} (Module.ran
k R p)
-/
lemma lift_cRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    lift.{um} (A.submatrix r c).cRank ≤ lift.{um₀} A.cRank := by
  have h : ((A.submatrix r id).submatrix id c).cRank ≤ (A.submatrix r id).cRank :=
    Submodule.rank_mono <| span_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m → R) →ₗ[R] (m₀ → R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span R (range A.col)) = span R (range (A.submatrix r id).col) := by
    simp_rw [LinearMap.map_span, ← image_univ, image_image, col_eq_transpose, transpose_submatrix]
    aesop
  rw [cRank, ← h_eq]
  have hwin := lift_rank_map_le f (span R (range Aᵀ))
  simp_rw [← lift_umax] at hwin ⊢
  exact hwin

/-- A special case of `lift_cRank_submatrix_le` for when `m₀` and `m` are in the same universe. -/
/-
**Matrix.cRank_submatrix_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cRank_submatrix_le {m m₀ : Type um} (A : Matrix m n R) (r : m₀ -> m) (c : 
n₀ -> n) : (A.submatrix r c).cRank <= A.cRank
参数：A : Matrix m n R；r : m₀ -> m；c : n₀ -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matrix.lift_cRank_submatrix_le`：lift_cRank_submatrix_le (A : Matrix m n 
R) (r : m₀ -> m) (c : n₀ -> n) : lift.{um} (A.submatrix r c).cRank <= lift.{um₀}
 A.cRank

--- 原说明 ---
A special case of `lift_cRank_submatrix_le` for when `m₀` and `m` are in the sam
e universe.
-/
lemma cRank_submatrix_le {m m₀ : Type um} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).cRank ≤ A.cRank := by
  simpa using lift_cRank_submatrix_le A r c
/-
**Matrix.cRank_le_card_height** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cRank_le_card_height [StrongRankCondition R] [Fintype m] (A : Matrix m n R
) : A.cRank <= Fintype.card m
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.rank_le`：Submodule.rank_le (s : Submodule R M) : Module.rank R
 s <= Module.rank R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_fun'`：rank_fun' : Module.rank R (η -> R) = Fintype.card η
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma cRank_le_card_height [StrongRankCondition R] [Fintype m] (A : Matrix m n R) :
    A.cRank ≤ Fintype.card m :=
  (Submodule.rank_le (span R (range Aᵀ))).trans <| by rw [rank_fun']
/-
**Matrix.cRank_le_card_width** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cRank_le_card_width [StrongRankCondition R] [Fintype n] (A : Matrix m n R)
 : A.cRank <= Fintype.card n
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
-/
lemma cRank_le_card_width [StrongRankCondition R] [Fintype n] (A : Matrix m n R) :
    A.cRank ≤ Fintype.card n :=
  (rank_span_le ..).trans <|
    by simpa [col_eq_transpose] using Cardinal.mk_range_le_lift (f := A.col)

/-- The rank of a matrix, defined as the dimension of its column space, as a term in `ℕ∞`. -/
/-
**Matrix.eRank** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：eRank (A : Matrix m n R) : Nat∞
参数：A : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a matrix, defined as the dimension of its column space, as a term in
 `ℕ∞`.
-/
noncomputable def eRank (A : Matrix m n R) : ℕ∞ := A.cRank.toENat

@[simp]
/-
**Matrix.eRank_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.eRank = 1
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cRank_subsingleton`：cRank_subsingleton [Subsingleton R] (A : Matr
ix m n R) : A.cRank = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.eRank = 1 := by
  simp [eRank]
/-
**Matrix.eRank_toNat_eq_finrank** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：eRank_toNat_eq_finrank (A : Matrix m n R) : A.eRank.toNat = Module.finrank
 R (span R (range A.col))
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_toENat`：∀ (a : Cardinal.{u_1}), (Cardinal.toENat a).toNat
 = Cardinal.toNat a
-/
lemma eRank_toNat_eq_finrank (A : Matrix m n R) :
    A.eRank.toNat = Module.finrank R (span R (range A.col)) :=
  toNat_toENat ..
/-
**Matrix.eRank_submatrix_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：eRank_submatrix_le (A : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n) : (A.sub
matrix r c).eRank <= A.eRank
参数：A : Matrix m n R；r : m₀ -> m；c : n₀ -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用引理 `Matrix.lift_cRank_submatrix_le`：lift_cRank_submatrix_le (A : Matrix m n 
R) (r : m₀ -> m) (c : n₀ -> n) : lift.{um} (A.submatrix r c).cRank <= lift.{um₀}
 A.cRank
-/
lemma eRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).eRank ≤ A.eRank := by
  simpa using! OrderHom.mono (β := ℕ∞) Cardinal.toENat <| lift_cRank_submatrix_le A r c
/-
**Matrix.eRank_le_card_width** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：eRank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.eRank <
= ENat.card n
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Matrix.eRank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : S
emiring R] (A : Matrix m n R), A.eRank = Cardinal.toENat A.cRank
· 使用定理 `Cardinal.toENat_le_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c ≤ ↑n ↔ c ≤ ↑n
· 使用引理 `Matrix.cRank_le_card_width`：cRank_le_card_width [StrongRankCondition R] 
[Fintype n] (A : Matrix m n R) : A.cRank <= Fintype.card n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.card_eq_top`：∀ {α : Type u_1}, ENat.card α = ⊤ ↔ Infinite α
-/
lemma eRank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card n := by
  wlog hfin : Finite n
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite n
  rw [ENat.card_eq_coe_fintype_card, eRank, toENat_le_natCast]
  exact A.cRank_le_card_width
/-
**Matrix.eRank_le_card_height** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：eRank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.eRank 
<= ENat.card m
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Matrix.eRank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : S
emiring R] (A : Matrix m n R), A.eRank = Cardinal.toENat A.cRank
· 使用定理 `Cardinal.toENat_le_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c ≤ ↑n ↔ c ≤ ↑n
· 使用引理 `Matrix.cRank_le_card_height`：cRank_le_card_height [StrongRankCondition R
] [Fintype m] (A : Matrix m n R) : A.cRank <= Fintype.card m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.card_eq_top`：∀ {α : Type u_1}, ENat.card α = ⊤ ↔ Infinite α
-/
lemma eRank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card m := by
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card, eRank, toENat_le_natCast]
  exact A.cRank_le_card_height

end Infinite

variable [Fintype n] [Fintype o]

/-- The rank of a matrix is the rank of its image. -/
/-
**Matrix.rank** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：rank [CommSemiring R] (A : Matrix m n R) : Nat
参数：A : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a matrix is the rank of its image.
-/
noncomputable def rank [CommSemiring R] (A : Matrix m n R) : ℕ :=
  finrank R <| LinearMap.range A.mulVecLin

@[simp]
/-
**Matrix.rank_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_subsingleton [CommSemiring R] [Subsingleton R] (A : Matrix m n R) : A
.rank = 1
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
-/
theorem rank_subsingleton [CommSemiring R] [Subsingleton R] (A : Matrix m n R) : A.rank = 1 :=
  finrank_subsingleton

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.cRank_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_one [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition
 R] : (cRank (1 : Matrix m m R)) = lift.{uR} #m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.linearIndependent_single_one`：linearIndependent_single_one (ι R : Typ
e*) [Semiring R] [DecidableEq ι] : LinearIndependent R (fun i : ι => Pi.single i
 (1 : R))
· 使用定理 `Matrix.cRank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : S
emiring R] (A : Matrix m n R),   A.cRank = Module.rank R ↥(Submodule.span R (Set
.range …
· 使用定理 `rank_span`：rank_span {v : ι -> M} (hv : LinearIndependent R v) : Module.
rank R ↑(span R (range v)) = #(range v)
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem cRank_one [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition R] :
    (cRank (1 : Matrix m m R)) = lift.{uR} #m := by
  have h : LinearIndependent R (1 : Matrix m m R).col := by
    convert! Pi.linearIndependent_single_one m R
    simp [funext_iff, one_apply, Pi.single_apply]
  rw [cRank, rank_span h, ← lift_umax, ← Cardinal.mk_range_eq_of_injective h.injective, lift_id']
/-
**Matrix.eRank_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type um} {R : Type uR} [inst : Semiring R] [Nontrivial R] [inst_2 :
 DecidableEq m] [StrongRankCondition R],   Matrix.eRank 1 = ENat.card m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.eRank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : S
emiring R] (A : Matrix m n R), A.eRank = Cardinal.toENat A.cRank
· 使用定理 `Matrix.cRank_one`：cRank_one [Semiring R] [Nontrivial R] [DecidableEq m] 
[StrongRankCondition R] : (cRank (1 : Matrix m m R)) = lift.{uR} #m
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `ENat.card.eq_1`：∀ (α : Type u_3), ENat.card α = Cardinal.toENat (Cardina
l.mk α)
-/
@[simp] theorem eRank_one [Semiring R] [Nontrivial R] [DecidableEq m] [StrongRankCondition R] :
    (eRank (1 : Matrix m m R)) = ENat.card m := by
  rw [eRank, cRank_one, toENat_lift, ENat.card]

@[simp]
/-
**Matrix.rank_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_one [CommSemiring R] [DecidableEq n] [StrongRankCondition R] : rank (
1 : Matrix n n R) = Fintype.card n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.mulVecLin_one`：Matrix.mulVecLin_one [DecidableEq n] : Matrix.mulV
ecLin (1 : Matrix n n R) = LinearMap.id
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `Module.finrank_pi`：Module.finrank_pi {ι : Type v} [Fintype ι] : finrank 
R (ι -> R) = Fintype.card ι
-/
theorem rank_one [CommSemiring R] [DecidableEq n] [StrongRankCondition R] :
    rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank, mulVecLin_one, LinearMap.range_id, finrank_top, finrank_pi]

@[simp]
/-
**Matrix.rank_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_zero [CommSemiring R] [Nontrivial R] : rank (0 : Matrix m n R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.mulVecLin_zero`：Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVec
Lin (0 : Matrix m n R) = 0
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
-/
theorem rank_zero [CommSemiring R] [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank, mulVecLin_zero, LinearMap.range_zero, finrank_bot]

@[simp]
/-
**Matrix.cRank_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : cRank (0 : Matrix m
 n R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cRank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : S
emiring R] (A : Matrix m n R),   A.cRank = Module.rank R ↥(Submodule.span R (Set
.range …
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `rank_bot`：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Matrix.col_eq_transpose`：col_eq_transpose (A : Matrix m n α) : A.col = o
f.symm Aᵀ
· 使用定理 `Matrix.transpose_zero`：transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0
· 使用定理 `Matrix.of_symm_zero`：of_symm_zero [Zero α] : of.symm (0 : Matrix m n α) 
= (0 : m -> n -> α)
· 使用定理 `Set.range_zero`：∀ {α : Type u_5} {β : Type u_6} [inst : Zero β] [Nonempt
y α], Set.range 0 = {0}
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
-/
theorem cRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : cRank (0 : Matrix m n R) = 0 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [cRank, range_eq_empty, span_empty, rank_bot]
  rw [cRank, col_eq_transpose, transpose_zero, of_symm_zero, range_zero, span_zero_singleton,
    rank_bot]

@[simp]
/-
**Matrix.eRank_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : eRank (0 : Matrix m
 n R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cRank_zero`：cRank_zero {m n : Type*} [Semiring R] [Nontrivial R] 
: cRank (0 : Matrix m n R) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : eRank (0 : Matrix m n R) = 0 := by
  simp [eRank]
/-
**Matrix.rank_le_card_width** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_le_card_width [CommSemiring R] [StrongRankCondition R] (A : Matrix m 
n R) : A.rank <= Fintype.card n
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LinearMap.finrank_range_le`：LinearMap.finrank_range_le [Module.Finite R 
M] (f : M ->ₗ[R] M') : finrank R (LinearMap.range f) <= finrank R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.finrank_pi`：Module.finrank_pi {ι : Type v} [Fintype ι] : finrank 
R (ι -> R) = Fintype.card ι
-/
theorem rank_le_card_width [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card n :=
  A.mulVecLin.finrank_range_le.trans_eq <| finrank_pi R
/-
**Matrix.rank_le_width** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_le_width [CommSemiring R] [StrongRankCondition R] {m n : Nat} (A : Ma
trix (Fin m) (Fin n) R) : A.rank <= n
参数：A : Matrix (Fin m) (Fin n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matrix.rank_le_card_width`：rank_le_card_width [CommSemiring R] [StrongRa
nkCondition R] (A : Matrix m n R) : A.rank <= Fintype.card n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem rank_le_width [CommSemiring R] [StrongRankCondition R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : A.rank ≤ n :=
  A.rank_le_card_width.trans <| (Fintype.card_fin n).le
/-
**Matrix.rank_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_le_left [CommSemiring R] [StrongRankCondition R] (A : Matrix m n 
R) (B : Matrix n o R) : (A * B).rank <= A.rank
参数：A : Matrix m n R；B : Matrix n o R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_subsingleton`：rank_subsingleton [CommSemiring R] [Subsinglet
on R] (A : Matrix m n R) : A.rank = 1
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.mulVecLin_mul`：Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R
) (N : Matrix m n R) : Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Mat
rix.mulVec…
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `LinearMap.rank_comp_le_left`：rank_comp_le_left (g : V ->ₗ[K] V') (f : V'
 ->ₗ[K] V'') : rank (f.comp g) <= rank f
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem rank_mul_le_left [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (B : Matrix n o R) : (A * B).rank ≤ A.rank := by
  nontriviality R
  rw [rank, rank, mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left ..) (rank_lt_aleph0 R _)
/-
**Matrix.rank_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_le_right [CommSemiring R] [StrongRankCondition R] (A : Matrix m n
 R) (B : Matrix n o R) : (A * B).rank <= B.rank
参数：A : Matrix m n R；B : Matrix n o R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_subsingleton`：rank_subsingleton [CommSemiring R] [Subsinglet
on R] (A : Matrix m n R) : A.rank = 1
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.mulVecLin_mul`：Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R
) (N : Matrix m n R) : Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Mat
rix.mulVec…
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用定理 `LinearMap.lift_rank_comp_le_right`：lift_rank_comp_le_right (g : V ->ₗ[K]
 V') (f : V' ->ₗ[K] V'') : Cardinal.lift.{v'} (rank (f.comp g)) <= Cardinal.lift
.{v''} (rank g)
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem rank_mul_le_right [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (B : Matrix n o R) : (A * B).rank ≤ B.rank := by
  nontriviality R
  rw [rank, rank, mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)
/-
**Matrix.rank_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_le [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) (B
 : Matrix n o R) : (A * B).rank <= min A.rank B.rank
参数：A : Matrix m n R；B : Matrix n o R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Matrix.rank_mul_le_left`：rank_mul_le_left [CommSemiring R] [StrongRankCo
ndition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= A.rank
· 使用定理 `Matrix.rank_mul_le_right`：rank_mul_le_right [CommSemiring R] [StrongRank
Condition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= B.rank
-/
theorem rank_mul_le [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)
/-
**Matrix.rank_vecMulVec_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_vecMulVec_le [CommSemiring R] [StrongRankCondition R] (w : m -> R) (v
 : n -> R) : (Matrix.vecMulVec w v).rank <= 1
参数：w : m -> R；v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMulVec_eq`：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (
w : m -> α) (v : n -> α) : vecMulVec w v = replicateCol ι w * replicateRow ι v
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Matrix.rank_mul_le_left`：rank_mul_le_left [CommSemiring R] [StrongRankCo
ndition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= A.rank
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.rank_subsingleton`：rank_subsingleton [CommSemiring R] [Subsinglet
on R] (A : Matrix m n R) : A.rank = 1
· 使用定理 `Matrix.rank_le_card_width`：rank_le_card_width [CommSemiring R] [StrongRa
nkCondition R] (A : Matrix m n R) : A.rank <= Fintype.card n
-/
theorem rank_vecMulVec_le [CommSemiring R] [StrongRankCondition R] (w : m → R) (v : n → R) :
    (Matrix.vecMulVec w v).rank ≤ 1 := by
  rw [Matrix.vecMulVec_eq Unit]
  refine le_trans (rank_mul_le_left _ _) ?_
  nontriviality R
  exact rank_le_card_width _
/-
**Matrix.rank_unit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_unit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : (M
atrix n n R)ˣ) : (A : Matrix n n R).rank = Fintype.card n
参数：A : (Matrix n n R)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Matrix.rank_le_card_width`：rank_le_card_width [CommSemiring R] [StrongRa
nkCondition R] (A : Matrix m n R) : A.rank <= Fintype.card n
· 使用定理 `Matrix.rank_mul_le_left`：rank_mul_le_left [CommSemiring R] [StrongRankCo
ndition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= A.rank
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_one`：rank_one [CommSemiring R] [DecidableEq n] [StrongRankCo
ndition R] : rank (1 : Matrix n n R) = Fintype.card n
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
-/
theorem rank_unit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n := by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, rank_one] at this
/-
**Matrix.rank_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_of_isUnit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A
 : Matrix n n R) (h : IsUnit A) : A.rank = Fintype.card n
参数：A : Matrix n n R；h : IsUnit A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.rank_unit`：rank_unit [DecidableEq n] [CommSemiring R] [StrongRank
Condition R] (A : (Matrix n n R)ˣ) : (A : Matrix n n R).rank = Fintype.card n
-/
theorem rank_of_isUnit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : Matrix n n R)
    (h : IsUnit A) : A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A
/-
**Matrix.rank_of_det_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Nontrivial R] [F
intype m] [DecidableEq m] {A : Matrix m m R} (hA : A.det in nonZeroDivisors R) :
 A.rank = Fintype.card m
参数：hA : A.det in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `LinearMap.finrank_range_of_inj`：LinearMap.finrank_range_of_inj {f : M ->
ₗ[R] N} (hf : Function.Injective f) : finrank R (LinearMap.range f) = finrank R 
M
· 使用定理 `Matrix.mulVec_injective_of_det_mem_nonZeroDivisors`：mulVec_injective_of_
det_mem_nonZeroDivisors (hM : M.det in R⁰) : Function.Injective M.mulVec
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem rank_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Nontrivial R]
    [Fintype m] [DecidableEq m] {A : Matrix m m R} (hA : A.det ∈ nonZeroDivisors R) :
    A.rank = Fintype.card m := by
  rw [rank, LinearMap.finrank_range_of_inj (mulVec_injective_of_det_mem_nonZeroDivisors hA),
    Module.finrank_eq_card_basis (Pi.basisFun R m)]
/-
**Matrix.rank_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [Dec
idableEq m] {A : Matrix m m R} (h : A.det != 0) : A.rank = Fintype.card m
参数：h : A.det != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.rank_of_det_mem_nonZeroDivisors`：rank_of_det_mem_nonZeroDivisors 
{R : Type*} [CommRing R] [Nontrivial R] [Fintype m] [DecidableEq m] {A : Matrix 
m m R} (hA : A.det in nonZer…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem rank_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [DecidableEq m]
    {A : Matrix m m R} (h : A.det ≠ 0) : A.rank = Fintype.card m :=
  rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)
/-
**Matrix.rank_smul_of_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：rank_smul_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {c : R} (B : Mat
rix m n R) (hc : c in nonZeroDivisors R) : (c • B).rank = B.rank
参数：B : Matrix m n R；hc : c in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSMulRegular_iff_mem_nonZeroSMulDivisors`：isSMulRegular_iff_mem_nonZero
SMulDivisors {M : Type*} [AddGroup M] [DistribMulAction M₀ M] {m₀ : M₀} : IsSMul
Regular M m₀ ↔ m₀ in nonZeroSMu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsSMulRegular.pi`：∀ {I : Type u} {f : I → Type v} {α : Type u_1} [inst :
 (i : I) → SMul α (f i)] {k : α},   (∀ (i : I), IsSMulRegular (f i) k) → IsSMulR
egular…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
lemma rank_smul_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {c : R} (B : Matrix m n R)
    (hc : c ∈ nonZeroDivisors R) : (c • B).rank = B.rank := by
  have hc' : IsSMulRegular R c := isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr hc.1
  have hreg : IsSMulRegular (m → R) c := IsSMulRegular.pi fun _ => hc'
  let f := LinearMap.lsmul R (m → R) c
  have hcomp : (c • B).mulVecLin = f.comp B.mulVecLin := by aesop
  rw [rank, rank, hcomp, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective f hreg _).finrank_eq.symm
/-
**Matrix.rank_mul_eq_left_of_det_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `
Matrix`。
形式化陈述：rank_mul_eq_left_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Deci
dableEq n] (A : Matrix n n R) (B : Matrix m n R) (hA : A.det in nonZeroDivisors 
R) : (B * A).rank = B.rank
参数：A : Matrix n n R；B : Matrix m n R；hA : A.det in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_subsingleton`：rank_subsingleton [CommSemiring R] [Subsinglet
on R] (A : Matrix m n R) : A.rank = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Matrix.rank_mul_le_left`：rank_mul_le_left [CommSemiring R] [StrongRankCo
ndition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= A.rank
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.rank_smul_of_mem_nonZeroDivisors`：rank_smul_of_mem_nonZeroDivisor
s {R : Type*} [CommRing R] {c : R} (B : Matrix m n R) (hc : c in nonZeroDivisors
 R) : (c • B).rank = B.rank
-/
lemma rank_mul_eq_left_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : A.det ∈ nonZeroDivisors R) :
    (B * A).rank = B.rank := by
  nontriviality R
  refine le_antisymm (rank_mul_le_left B A) ?_
  have key : (B * A) * A.adjugate = A.det • B := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  calc B.rank = (A.det • B).rank := (rank_smul_of_mem_nonZeroDivisors B hA).symm
    _ = ((B * A) * A.adjugate).rank := by rw [key]
    _ ≤ (B * A).rank := rank_mul_le_left _ _
/-
**Matrix.rank_mul_eq_left_of_det_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_eq_left_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Dec
idableEq n] (A : Matrix n n R) (B : Matrix m n R) (h : A.det != 0) : (B * A).ran
k = B.rank
参数：A : Matrix n n R；B : Matrix m n R；h : A.det != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.rank_mul_eq_left_of_det_mem_nonZeroDivisors`：rank_mul_eq_left_of_
det_mem_nonZeroDivisors {R : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n
 R) (B : Matrix m n R) (hA : A.det in no…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
lemma rank_mul_eq_left_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (h : A.det ≠ 0) : (B * A).rank = B.rank :=
  rank_mul_eq_left_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

/-- Right multiplying by an invertible matrix does not change the rank -/
@[simp]
/-
**Matrix.rank_mul_eq_left_of_isUnit_det** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_eq_left_of_isUnit_det {R : Type*} [CommRing R] [DecidableEq n] (A
 : Matrix n n R) (B : Matrix m n R) (hA : IsUnit A.det) : (B * A).rank = B.rank
参数：A : Matrix n n R；B : Matrix m n R；hA : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.rank_mul_eq_left_of_det_mem_nonZeroDivisors`：rank_mul_eq_left_of_
det_mem_nonZeroDivisors {R : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n
 R) (B : Matrix m n R) (hA : A.det in no…
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰

--- 原说明 ---
Right multiplying by an invertible matrix does not change the rank
-/
lemma rank_mul_eq_left_of_isUnit_det {R : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n R)
    (B : Matrix m n R) (hA : IsUnit A.det) : (B * A).rank = B.rank :=
  rank_mul_eq_left_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors
/-
**Matrix.rank_mul_eq_right_of_det_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 
`Matrix`。
形式化陈述：rank_mul_eq_right_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Fin
type m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R) (hA : A.det in non
ZeroDivisors R) : (A * B).rank = B.rank
参数：A : Matrix m m R；B : Matrix m n R；hA : A.det in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.mulVecLin_mul`：Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R
) (N : Matrix m n R) : Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Mat
rix.mulVec…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Matrix.mulVec_injective_of_det_mem_nonZeroDivisors`：mulVec_injective_of_
det_mem_nonZeroDivisors (hM : M.det in R⁰) : Function.Injective M.mulVec
-/
lemma rank_mul_eq_right_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.det ∈ nonZeroDivisors R) : (A * B).rank = B.rank := by
  rw [rank, rank, mulVecLin_mul, LinearMap.range_comp,
    ← (Submodule.equivMapOfInjective A.mulVecLin
      (mulVec_injective_of_det_mem_nonZeroDivisors hA) _).finrank_eq]
/-
**Matrix.rank_mul_eq_right_of_det_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_eq_right_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Fi
ntype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R) (h : A.det != 0) 
: (A * B).rank = B.rank
参数：A : Matrix m m R；B : Matrix m n R；h : A.det != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.rank_mul_eq_right_of_det_mem_nonZeroDivisors`：rank_mul_eq_right_o
f_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Fintype m] [DecidableEq m] (
A : Matrix m m R) (B : Matrix m n R) (hA …
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
lemma rank_mul_eq_right_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R) (h : A.det ≠ 0) :
    (A * B).rank = B.rank :=
  rank_mul_eq_right_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

/-- Left multiplying by an invertible matrix does not change the rank -/
@[simp]
/-
**Matrix.rank_mul_eq_right_of_isUnit_det** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：rank_mul_eq_right_of_isUnit_det {R : Type*} [CommRing R] [Fintype m] [Deci
dableEq m] (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) : (A * B).r
ank = B.rank
参数：A : Matrix m m R；B : Matrix m n R；hA : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.rank_mul_eq_right_of_det_mem_nonZeroDivisors`：rank_mul_eq_right_o
f_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Fintype m] [DecidableEq m] (
A : Matrix m m R) (B : Matrix m n R) (hA …
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰

--- 原说明 ---
Left multiplying by an invertible matrix does not change the rank
-/
lemma rank_mul_eq_right_of_isUnit_det {R : Type*} [CommRing R] [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) : (A * B).rank = B.rank :=
  rank_mul_eq_right_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors
/-
**Matrix.rank_mul_eq_right_of_isLowerTriangular** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x`。
形式化陈述：rank_mul_eq_right_of_isLowerTriangular {R : Type*} [CommRing R] [IsDomain 
R] [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R) (hA : A.IsL
owerTriangular) (hd : forall i, A.diag i != 0) : (A * B).rank = B.rank
参数：A : Matrix m m R；B : Matrix m n R；hA : A.IsLowerTriangular；hd : forall i, A.d
iag i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_of_isLowerTriangular`：det_of_isLowerTriangular [LinearOrder m
] (M : Matrix m m R) (h : M.IsLowerTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Matrix.rank_mul_eq_right_of_det_ne_zero`：rank_mul_eq_right_of_det_ne_zer
o {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [DecidableEq m] (A : Matrix 
m m R) (B : Matrix m n R) (h …
-/
lemma rank_mul_eq_right_of_isLowerTriangular {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.IsLowerTriangular) (hd : ∀ i, A.diag i ≠ 0) : (A * B).rank = B.rank := by
  have hdet : A.det ≠ 0 := by simpa [det_of_isLowerTriangular A hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet
/-
**Matrix.rank_mul_eq_right_of_isUpperTriangular** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x`。
形式化陈述：rank_mul_eq_right_of_isUpperTriangular {R : Type*} [CommRing R] [IsDomain 
R] [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R) (hA : A.IsU
pperTriangular) (hd : forall i, A.diag i != 0) : (A * B).rank = B.rank
参数：A : Matrix m m R；B : Matrix m n R；hA : A.IsUpperTriangular；hd : forall i, A.d
iag i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Matrix.rank_mul_eq_right_of_det_ne_zero`：rank_mul_eq_right_of_det_ne_zer
o {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [DecidableEq m] (A : Matrix 
m m R) (B : Matrix m n R) (h …
-/
lemma rank_mul_eq_right_of_isUpperTriangular {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.IsUpperTriangular) (hd : ∀ i, A.diag i ≠ 0) : (A * B).rank = B.rank := by
  have hdet : A.det ≠ 0 := by simpa [det_of_isUpperTriangular hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

/-- Taking a subset of the rows and columns reduces the rank. -/
/-
**Matrix.rank_submatrix_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_submatrix_le [CommSemiring R] [StrongRankCondition R] [Fintype n₀] (A
 : Matrix m n R) (r : m₀ -> m) (c : n₀ -> n) : (A.submatrix r c).rank <= A.rank
参数：A : Matrix m n R；r : m₀ -> m；c : n₀ -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_subsingleton`：rank_subsingleton [CommSemiring R] [Subsinglet
on R] (A : Matrix m n R) : A.rank = 1
· 使用定理 `Module.Finite.span_of_finite`：span_of_finite {A : Set M} (hA : Set.Finit
e A) : Module.Finite R (span R A)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.mulVecLin_transpose`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : Fintype m] (M : Matrix m n R),   M.transpos
e.mulVecLin = M.…
· 使用定理 `range_vecMulLinear`：range_vecMulLinear (M : Matrix m n R) : LinearMap.ra
nge M.vecMulLinear = span R (range M.row)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.row_transpose`：row_transpose (A : Matrix m n α) : Aᵀ.row = A.col
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.mulVecLin_submatrix`：Matrix.mulVecLin_submatrix [Fintype n] [Fint
ype l] (f₁ : m -> k) (e₂ : n ≃ l) (M : Matrix k l R) : (M.submatrix f₁ e₂).mulVe
cLin = funLeft R…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Taking a subset of the rows and columns reduces the rank.
-/
theorem rank_submatrix_le [CommSemiring R] [StrongRankCondition R] [Fintype n₀] (A : Matrix m n R)
    (r : m₀ → m) (c : n₀ → n) : (A.submatrix r c).rank ≤ A.rank := by
  nontriviality R
  have := Module.Finite.span_of_finite R (Set.finite_range (A.submatrix r id).col)
  calc
    _ = (((A.submatrix r id)ᵀᵀ.submatrix id c)ᵀᵀ).rank := by simp
    _ ≤ finrank R (span R (range (A.submatrix r id).col)) := by
      rw [rank, Matrix.mulVecLin_transpose, Matrix.transpose_submatrix, transpose_transpose,
        range_vecMulLinear, ← Matrix.transpose_submatrix, row_transpose]
      exact Submodule.finrank_mono (Submodule.span_mono (fun v ⟨j, hj⟩ => ⟨c j, hj⟩))
    _ = (A.submatrix r id)ᵀᵀ.rank := by
      rw [rank, Matrix.mulVecLin_transpose, range_vecMulLinear]
      rfl
    _ = (A.submatrix r (Equiv.refl n)).rank := by simp
  rw [rank, rank, mulVecLin_submatrix, LinearMap.range_comp, LinearMap.range_comp,
    show LinearMap.funLeft R R (Equiv.refl n).symm = LinearEquiv.funCongrLeft R R
      (Equiv.refl n).symm from rfl, LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _
/-
**Matrix.rank_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_reindex [Fintype n₀] [CommSemiring R] (em : m ≃ m₀) (en : n ≃ n₀) (A 
: Matrix m n R) : rank (A.reindex em en) = rank A
参数：em : m ≃ m₀；en : n ≃ n₀；A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.mulVecLin_reindex`：Matrix.mulVecLin_reindex [Fintype n] [Fintype 
l] (e₁ : k ≃ m) (e₂ : l ≃ n) (M : Matrix k l R) : (reindex e₁ e₂ M).mulVecLin = 
↑(LinearEquiv.…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearEquiv.finrank_map_eq`：finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodul
e R M) : finrank R (p.map (f : M ->ₗ[R] N)) = finrank R p
-/
theorem rank_reindex [Fintype n₀] [CommSemiring R] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n R) :
    rank (A.reindex em en) = rank A := by
  rw [rank, rank, mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

@[simp]
/-
**Matrix.rank_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_submatrix [Fintype n₀] [CommSemiring R] (A : Matrix m n R) (em : m₀ ≃
 m) (en : n₀ ≃ n) : rank (A.submatrix em en) = rank A
参数：A : Matrix m n R；em : m₀ ≃ m；en : n₀ ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.rank_reindex`：rank_reindex [Fintype n₀] [CommSemiring R] (em : m 
≃ m₀) (en : n ≃ n₀) (A : Matrix m n R) : rank (A.reindex em en) = rank A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem rank_submatrix [Fintype n₀] [CommSemiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : rank (A.submatrix em en) = rank A := by
  simpa only [reindex_apply] using! rank_reindex em.symm en.symm A

@[simp]
/-
**Matrix.lift_cRank_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：lift_cRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m
₀ ≃ m) (en : n₀ ≃ n) : lift.{um} (cRank (A.submatrix em en)) = lift.{um₀} (cRank
 A)
参数：A : Matrix m n R；em : m₀ ≃ m；en : n₀ ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matrix.lift_cRank_submatrix_le`：lift_cRank_submatrix_le (A : Matrix m n 
R) (r : m₀ -> m) (c : n₀ -> n) : lift.{um} (A.submatrix r c).cRank <= lift.{um₀}
 A.cRank
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
-/
theorem lift_cRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : lift.{um} (cRank (A.submatrix em en)) = lift.{um₀} (cRank A) :=
  (A.lift_cRank_submatrix_le em en).antisymm
    <| by simpa using ((A.reindex em.symm en.symm).lift_cRank_submatrix_le em.symm en.symm)

/-- A special case of `lift_cRank_submatrix` for when the row types are in the same universe. -/
@[simp]
/-
**Matrix.cRank_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_submatrix {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n 
R) (em : m₀ ≃ m) (en : n₀ ≃ n) : cRank (A.submatrix em en) = cRank A
参数：A : Matrix m n R；em : m₀ ≃ m；en : n₀ ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.lift_cRank_submatrix`：lift_cRank_submatrix {n : Type un} [Semirin
g R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) : lift.{um} (cRank (A.submat
rix em en)) = lif…

--- 原说明 ---
A special case of `lift_cRank_submatrix` for when the row types are in the same 
universe.
-/
theorem cRank_submatrix {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : cRank (A.submatrix em en) = cRank A := by
  simpa [-lift_cRank_submatrix] using A.lift_cRank_submatrix em en
/-
**Matrix.lift_cRank_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：lift_cRank_reindex {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃
 m₀) (en : n ≃ n₀) : lift.{um} (cRank (A.reindex em en)) = lift.{um₀} (cRank A)
参数：A : Matrix m n R；em : m ≃ m₀；en : n ≃ n₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.lift_cRank_submatrix`：lift_cRank_submatrix {n : Type un} [Semirin
g R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) : lift.{um} (cRank (A.submat
rix em en)) = lif…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_cRank_reindex {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : lift.{um} (cRank (A.reindex em en)) = lift.{um₀} (cRank A) :=
  lift_cRank_submatrix ..

/-- A special case of `lift_cRank_reindex` for when the row types are in the same universe. -/
/-
**Matrix.cRank_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R)
 (em : m ≃ m₀) (en : n ≃ n₀) : cRank (A.reindex em en) = cRank A
参数：A : Matrix m n R；em : m ≃ m₀；en : n ≃ n₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.cRank_submatrix`：cRank_submatrix {m₀ : Type um} {n : Type un} [Se
miring R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) : cRank (A.submatrix em
 en) = cRank…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A special case of `lift_cRank_reindex` for when the row types are in the same un
iverse.
-/
theorem cRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : cRank (A.reindex em en) = cRank A :=
  cRank_submatrix ..

@[simp]
/-
**Matrix.eRank_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m
) (en : n₀ ≃ n) : eRank (A.submatrix em en) = eRank A
参数：A : Matrix m n R；em : m₀ ≃ m；en : n₀ ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.lift_cRank_submatrix`：lift_cRank_submatrix {n : Type un} [Semirin
g R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) : lift.{um} (cRank (A.submat
rix em en)) = lif…
-/
theorem eRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    eRank (A.submatrix em en) = eRank A := by
  simpa [-lift_cRank_submatrix] using! congr_arg Cardinal.toENat <| A.lift_cRank_submatrix em en
/-
**Matrix.eRank_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R)
 (em : m ≃ m₀) (en : n ≃ n₀) : eRank (A.reindex em en) = eRank A
参数：A : Matrix m n R；em : m ≃ m₀；en : n ≃ n₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.eRank_submatrix`：eRank_submatrix {n : Type un} [Semiring R] (A : 
Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) : eRank (A.submatrix em en) = eRank A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem eRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : eRank (A.reindex em en) = eRank A :=
  eRank_submatrix ..

set_option backward.isDefEq.respectTransparency false in
/-- The rank of a matrix equals the dimension of the range of the corresponding linear map,
and is therefore independent of the choice of bases. -/
/-
**Matrix.rank_eq_finrank_range_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [Co
mmSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] 
(A : Matrix m n R) (v₁ : Basis m R M₁) (v₂ : Basis n R M₂) : A.rank = finrank R 
(LinearMap.range (toLin v₂ v₁ A))
参数：A : Matrix m n R；v₁ : Basis m R M₁；v₂ : Basis n R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.toLin'_apply'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type
 u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix
 m n R), M…
· 使用定理 `Matrix.toLin_eq_toLin'`：Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisF
un R n) (Pi.basisFun R m) = Matrix.toLin'
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rank of a matrix equals the dimension of the range of the corresponding line
ar map,
and is therefore independent of the choice of bases.
-/
theorem rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R)
    (v₁ : Basis m R M₁) (v₂ : Basis n R M₂) :
    A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A)) := by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) e₂.range]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := toLin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [toLin_eq_toLin', toLin'_apply'] at aux₁
  rw [Pi.basisFun_apply] at aux₁ aux₂
  simp only [e₁, e₂, LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.refl_apply,
    aux₁, aux₂, LinearMap.coe_single, toLin_self, map_sum, map_smul, Basis.equiv_apply]
/-
**Matrix.rank_le_card_height** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_le_card_height [Fintype m] [CommSemiring R] [StrongRankCondition R] (
A : Matrix m n R) : A.rank <= Fintype.card m
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Module.finrank_pi`：Module.finrank_pi {ι : Type v} [Fintype ι] : finrank 
R (ι -> R) = Fintype.card ι
-/
theorem rank_le_card_height [Fintype m] [CommSemiring R] [StrongRankCondition R]
    (A : Matrix m n R) : A.rank ≤ Fintype.card m :=
  (Submodule.finrank_le _).trans (finrank_pi R).le

/-- The rank of a matrix is at most the size of any finset containing all its nonzero rows. -/
/-
**Matrix.rank_le_card_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_le_card_of_support_subset [CommSemiring R] [StrongRankCondition R] (A
 : Matrix m n R) (s : Finset m) (hz : Function.support A.row subseteq s) : A.ran
k <= s.card
参数：A : Matrix m n R；s : Finset m；hz : Function.support A.row subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.rank_mul_le_right`：rank_mul_le_right [CommSemiring R] [StrongRank
Condition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= B.rank
· 使用定理 `Matrix.rank_le_card_height`：rank_le_card_height [Fintype m] [CommSemirin
g R] [StrongRankCondition R] (A : Matrix m n R) : A.rank <= Fintype.card m
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s

--- 原说明 ---
The rank of a matrix is at most the size of any finset containing all its nonzer
o rows.
-/
theorem rank_le_card_of_support_subset [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (s : Finset m) (hz : Function.support A.row ⊆ s) : A.rank ≤ s.card := by
  rw [Function.support_subset_iff'] at hz
  classical
  set B : Matrix m {x // x ∈ s} R := Matrix.of fun i a => if (a : m) = i then 1 else 0 with hBdef
  have hB : B * A.submatrix Subtype.val id = A := by
    ext i j
    simp only [hBdef, mul_apply, of_apply, submatrix_apply, id_eq]
    by_cases hi : i ∈ s
    · rw [Fintype.sum_eq_single (⟨i, hi⟩ : {x // x ∈ s})
        fun a ha => by rw [if_neg fun he => ha (Subtype.ext he), zero_mul], if_pos rfl, one_mul]
    · have h0 : A i = 0 := hz i hi
      aesop
  calc A.rank = (B * A.submatrix Subtype.val id).rank := by rw [hB]
    _ ≤ (A.submatrix Subtype.val id).rank := rank_mul_le_right _ _
    _ ≤ Fintype.card {x // x ∈ s} := rank_le_card_height _
    _ = s.card := Fintype.card_coe s
/-
**Matrix.rank_le_height** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_le_height [CommSemiring R] [StrongRankCondition R] {m n : Nat} (A : M
atrix (Fin m) (Fin n) R) : A.rank <= m
参数：A : Matrix (Fin m) (Fin n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matrix.rank_le_card_height`：rank_le_card_height [Fintype m] [CommSemirin
g R] [StrongRankCondition R] (A : Matrix m n R) : A.rank <= Fintype.card m
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem rank_le_height [CommSemiring R] [StrongRankCondition R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : A.rank ≤ m :=
  A.rank_le_card_height.trans (Fintype.card_fin m).le

/-- The rank of a matrix is the rank of the space spanned by its columns. -/
/-
**Matrix.rank_eq_finrank_span_cols** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_eq_finrank_span_cols [CommSemiring R] (A : Matrix m n R) : A.rank = f
inrank R (Submodule.span R (Set.range A.col))
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Matrix.range_mulVecLin`：Matrix.range_mulVecLin (M : Matrix m n R) : Line
arMap.range M.mulVecLin = span R (range M.col)

--- 原说明 ---
The rank of a matrix is the rank of the space spanned by its columns.
-/
theorem rank_eq_finrank_span_cols [CommSemiring R] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.col)) := by rw [rank, Matrix.range_mulVecLin]

@[simp]
/-
**Matrix.cRank_toNat_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.cRank.toNat = 
A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.cRank_toNat_eq_finrank`：cRank_toNat_eq_finrank (A : Matrix m n R)
 : A.cRank.toNat = Module.finrank R (span R (range A.col))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.rank_eq_finrank_span_cols`：rank_eq_finrank_span_cols [CommSemirin
g R] (A : Matrix m n R) : A.rank = finrank R (Submodule.span R (Set.range A.col)
)
-/
theorem cRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.cRank.toNat = A.rank := by
  rw [cRank_toNat_eq_finrank, ← rank_eq_finrank_span_cols]

@[simp]
/-
**Matrix.eRank_toNat_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.eRank.toNat = 
A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.eRank_toNat_eq_finrank`：eRank_toNat_eq_finrank (A : Matrix m n R)
 : A.eRank.toNat = Module.finrank R (span R (range A.col))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.rank_eq_finrank_span_cols`：rank_eq_finrank_span_cols [CommSemirin
g R] (A : Matrix m n R) : A.rank = finrank R (Submodule.span R (Set.range A.col)
)
-/
theorem eRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [eRank_toNat_eq_finrank, ← rank_eq_finrank_span_cols]

section Field

variable [Field R]

/-- The rank of a diagonal matrix is the count of non-zero elements on its main diagonal -/
/-
**Matrix.rank_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_diagonal [Fintype m] [DecidableEq m] [DecidableEq R] (w : m -> R) : (
diagonal w).rank = Fintype.card {i // (w i) != 0}
参数：w : m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin'_apply'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type
 u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix
 m n R), M…
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `LinearMap.rank.eq_1`：∀ {K : Type u} {V : Type v} {V' : Type v'} [inst : 
Semiring K] [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module K V]   [inst_3 : 
AddCommMo…
· 使用定理 `LinearMap.rank_diagonal`：rank_diagonal [DecidableEq m] [DecidableEq K] (
w : m -> K) : LinearMap.rank (toLin' (diagonal w)) = Fintype.card { i // w i != 
0 }
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n

--- 原说明 ---
The rank of a diagonal matrix is the count of non-zero elements on its main diag
onal
-/
theorem rank_diagonal [Fintype m] [DecidableEq m] [DecidableEq R] (w : m → R) :
    (diagonal w).rank = Fintype.card {i // (w i) ≠ 0} := by
  rw [Matrix.rank, ← Matrix.toLin'_apply', Module.finrank, ← LinearMap.rank,
    LinearMap.rank_diagonal, Cardinal.toNat_natCast]

open TransvectionStruct in
/-- Every square matrix over a field can be brought, by left and right multiplication by
invertible matrices, into the block form `fromBlocks 1 0 0 0`, where the identity block has size
equal to the rank of the matrix. -/
/-
**Matrix.exists_rank_normal_form** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exists_rank_normal_form [Fintype m] [DecidableEq m] (M : Matrix m m R) : e
xists (V U : Matrix m m R) (e : m ≃ Fin M.rank oplus Fin (Fintype.card m - M.ran
k)), IsUnit V ∧ IsUnit U ∧ V * M * U = (fromBlocks 1 0 0 0).submatrix e e
参数：M : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`：exists
_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) : exists (L L' 
: List (TransvectionStruct n 𝕜)) (D : n -> 𝕜), M = (L.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Matrix.TransvectionStruct.isUnit_prod_comp_inverse`：isUnit_prod_comp_inv
erse (L : List (TransvectionStruct n R)) : IsUnit (L.map (toMatrix ∘ .inv)).prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Matrix.TransvectionStruct.prod_mul_reverse_inv_prod`：prod_mul_reverse_in
v_prod (L : List (TransvectionStruct n R)) : (L.map toMatrix).prod * (L.reverse.
map (toMatrix ∘ TransvectionStruct.inv)).…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.TransvectionStruct.reverse_inv_prod_mul_prod`：reverse_inv_prod_mu
l_prod (L : List (TransvectionStruct n R)) : (L.reverse.map (toMatrix ∘ Transvec
tionStruct.inv)).prod * (L.map toMatrix).…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Every square matrix over a field can be brought, by left and right multiplicatio
n by
invertible matrices, into the block form `fromBlocks 1 0 0 0`, where the identit
y block has size
equal to the rank of the matrix.
-/
theorem exists_rank_normal_form [Fintype m] [DecidableEq m] (M : Matrix m m R) :
    ∃ (V U : Matrix m m R) (e : m ≃ Fin M.rank ⊕ Fin (Fintype.card m - M.rank)),
      IsUnit V ∧ IsUnit U ∧
      V * M * U = (fromBlocks 1 0 0 0).submatrix e e := by
  classical
  obtain ⟨L, L', D, hM0⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  set E := fun i ↦ if D i = 0 then 1 else (D i)⁻¹ with E_def
  set s : Finset m := .filter (fun i ↦ D i ≠ 0) .univ with s_def
  set V := diagonal E * (L.reverse.map (toMatrix ∘ .inv)).prod with V_def
  set U := (L'.reverse.map (toMatrix ∘ .inv)).prod with U_def
  have hUdet : IsUnit U.det := (isUnit_iff_isUnit_det _).1 <| isUnit_prod_comp_inverse _
  have hVdet : IsUnit V.det := by
    rw [V_def, det_mul, det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 (by grind)) |>.mul <|
      (isUnit_iff_isUnit_det _).1 (isUnit_prod_comp_inverse _)
  have hM : V * M * U = diagonal (fun i ↦ if i ∈ s then 1 else 0) := by
    rw [V_def, U_def, hM0, mul_assoc, mul_assoc _ (L'.map _).prod, prod_mul_reverse_inv_prod,
      mul_one, ← mul_assoc, mul_assoc _ (L.reverse.map _).prod, reverse_inv_prod_mul_prod, mul_one]
    ext
    simp only [E_def, mul_diagonal, diagonal_apply, ite_mul, one_mul, zero_mul, s_def,
      Finset.mem_filter, Finset.mem_univ, true_and, ite_not]
    split_ifs with h1 h2 <;> first | rw [← h1, h2] | rw [← h1, inv_mul_cancel₀ h2] | rfl
  have hs : s.card = M.rank := by
    simp [← rank_mul_eq_right_of_isUnit_det V M hVdet, ← rank_mul_eq_left_of_isUnit_det U (V * M)
      hUdet, hM, rank_diagonal]
  set e : m ≃ Fin M.rank ⊕ Fin (Fintype.card m - M.rank) :=
    (Equiv.sumCompl (· ∈ s)).symm.trans <| (Finset.equivFinOfCardEq hs).sumCongr <|
      Fintype.equivFinOfCardEq <| by rw [Fintype.card_subtype_compl, Fintype.card_coe, hs] with he
  refine ⟨V, U, e, (isUnit_iff_isUnit_det _).2 hVdet, isUnit_prod_comp_inverse _, ?_⟩
  rw [hM, ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, submatrix_diagonal_equiv]
  refine congrArg _ (funext fun i ↦ ?_)
  split_ifs with hi <;> simp [he, hi]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.cRank_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cRank_diagonal [DecidableEq m] (w : m -> R) : (diagonal w).cRank = lift.{u
R} #{i // (w i) != 0}
参数：w : m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.linearIndependent_single_of_ne_zero`：linearIndependent_single_of_ne_z
ero [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [IsTorsionFree R M] [Dec
idableEq ι] {v : ι -> M} (hv…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Pi.single_congr`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] {i₁ i₂ : ι},   i₁ = i₂ → ∀ {x₁ x₂ : M}, x₁ = x₂ → ∀ {j₁ j₂ : ι
}, j₁…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
（共 43 条，此处仅展示前 30 条）
-/
theorem cRank_diagonal [DecidableEq m] (w : m → R) :
    (diagonal w).cRank = lift.{uR} #{i // (w i) ≠ 0} := by
  classical
  set w' : {i // (w i) ≠ 0} → _ := fun i ↦ (diagonal w) i
  have h : LinearIndependent R w' := by
    have hli' := Pi.linearIndependent_single_of_ne_zero (R := R)
      (v := fun i : m ↦ if w i = 0 then (1 : R) else w i) (by simp [ite_eq_iff'])
    convert! hli'.comp Subtype.val Subtype.val_injective
    ext ⟨j, hj⟩ k
    simp [w', diagonal, hj, Pi.single_apply, eq_comm]
  have hrw : insert 0 (range (diagonal w).col) = insert 0 (range w') := by
    suffices ∀ a, diagonal w a = 0 ∨ ∃ b, w b ≠ 0 ∧ diagonal w b = diagonal w a
      by aesop (add simp [col_eq_transpose, subset_def])
    simp_rw [or_iff_not_imp_right, not_exists, not_and, not_imp_not]
    simp +contextual [funext_iff, diagonal]
  rw [cRank, ← span_insert_zero, hrw, span_insert_zero, rank_span h,
    ← lift_umax, ← Cardinal.mk_range_eq_of_injective h.injective, lift_id']
/-
**Matrix.eRank_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eRank_diagonal [DecidableEq m] (w : m -> R) : (diagonal w).eRank = {i | (w
 i) != 0}.encard
参数：w : m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cRank_diagonal`：cRank_diagonal [DecidableEq m] (w : m -> R) : (di
agonal w).cRank = lift.{uR} #{i // (w i) != 0}
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eRank_diagonal [DecidableEq m] (w : m → R) :
    (diagonal w).eRank = {i | (w i) ≠ 0}.encard := by
  simp [eRank, cRank_diagonal, toENat_cardinalMk_subtype]

end Field

/-! ### Lemmas about transpose and conjugate transpose

This section contains lemmas about the rank of `Matrix.transpose` and `Matrix.conjTranspose`.

Unfortunately the proofs are essentially duplicated between the two; `ℚ` is a linearly-ordered ring
but can't be a star-ordered ring, while `ℂ` is star-ordered (with `open ComplexOrder`) but
not linearly ordered. For now we don't prove the transpose case for `ℂ`.

TODO: the lemmas `Matrix.rank_transpose` and `Matrix.rank_conjTranspose` current follow a short
proof that is a simple consequence of `Matrix.rank_transpose_mul_self` and
`Matrix.rank_conjTranspose_mul_self`. This proof pulls in unnecessary assumptions on `R`, and should
be replaced with a proof that uses Gaussian reduction or argues via linear combinations.
-/

section StarOrderedField

variable [Fintype m] [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/-
**Matrix.ker_mulVecLin_conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：ker_mulVecLin_conjTranspose_mul_self (A : Matrix m n R) : LinearMap.ker (A
ᴴ * A).mulVecLin = LinearMap.ker (mulVecLin A)
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_mulVecLin_conjTranspose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᴴ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, conjTranspose_mul_self_mulVec_eq_zero]
/-
**Matrix.rank_conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_conjTranspose_mul_self (A : Matrix m n R) : (Aᴴ * A).rank = A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.ker_mulVecLin_conjTranspose_mul_self`：ker_mulVecLin_conjTranspose
_mul_self (A : Matrix m n R) : LinearMap.ker (Aᴴ * A).mulVecLin = LinearMap.ker 
(mulVecLin A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_conjTranspose_mul_self (A : Matrix m n R) : (Aᴴ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) ?_
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᴴ * A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ * A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

-- this follows the proof here https://math.stackexchange.com/a/81903/1896
/-- TODO: prove this in greater generality. -/
@[simp]
/-
**Matrix.rank_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_conjTranspose (A : Matrix m n R) : Aᴴ.rank = A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.rank_conjTranspose_mul_self`：rank_conjTranspose_mul_self (A : Mat
rix m n R) : (Aᴴ * A).rank = A.rank
· 使用定理 `Matrix.rank_mul_le_left`：rank_mul_le_left [CommSemiring R] [StrongRankCo
ndition R] (A : Matrix m n R) (B : Matrix n o R) : (A * B).rank <= A.rank
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M

--- 原说明 ---
TODO: prove this in greater generality.
-/
theorem rank_conjTranspose (A : Matrix m n R) : Aᴴ.rank = A.rank :=
  le_antisymm
    (((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
      congr_arg _ <| conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]
/-
**Matrix.rank_self_mul_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_self_mul_conjTranspose (A : Matrix m n R) : (A * Aᴴ).rank = A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.rank_conjTranspose`：rank_conjTranspose (A : Matrix m n R) : Aᴴ.ra
nk = A.rank
· 使用定理 `Matrix.rank_conjTranspose_mul_self`：rank_conjTranspose_mul_self (A : Mat
rix m n R) : (Aᴴ * A).rank = A.rank
-/
theorem rank_self_mul_conjTranspose (A : Matrix m n R) : (A * Aᴴ).rank = A.rank := by
  simpa only [rank_conjTranspose, conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self Aᴴ

end StarOrderedField

section LinearOrderedField

variable [Fintype m] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-
**Matrix.ker_mulVecLin_transpose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ker_mulVecLin_transpose_mul_self (A : Matrix m n R) : LinearMap.ker (Aᵀ * 
A).mulVecLin = LinearMap.ker (mulVecLin A)
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `dotProduct_self_eq_zero`：dotProduct_self_eq_zero [Ring R] [LinearOrder R
] [IsStrictOrderedRing R] {v : n -> R} : v ⬝ᵥ v = 0 ↔ v = 0
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Matrix.mulVec_zero`：mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 
= 0
-/
theorem ker_mulVecLin_transpose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h, mulVec_zero]
/-
**Matrix.rank_transpose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_transpose_mul_self (A : Matrix m n R) : (Aᵀ * A).rank = A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.ker_mulVecLin_transpose_mul_self`：ker_mulVecLin_transpose_mul_sel
f (A : Matrix m n R) : LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker (mulVecL
in A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_transpose_mul_self (A : Matrix m n R) : (Aᵀ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) ?_
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᵀ * A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᵀ * A)) }
  · rw [ker_mulVecLin_transpose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

end LinearOrderedField

@[simp]
/-
**Matrix.rank_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_transpose [Field R] [Fintype m] (A : Matrix m n R) : Aᵀ.rank = A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_eq_finrank_range_toLin`：rank_eq_finrank_range_toLin [Finite 
m] [DecidableEq n] {M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommM
onoid M₂] [Module R M₁] …
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Matrix.toLin_transpose`：Matrix.toLin_transpose (M : Matrix ι₁ ι₂ K) : Ma
trix.toLin B₁.dualBasis B₂.dualBasis Mᵀ = Module.Dual.transpose (R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.dualMap_def`：LinearMap.dualMap_def (f : M₁ ->ₗ[R] M₂) : f.dual
Map = Module.Dual.transpose f
· 使用定理 `LinearMap.finrank_range_dualMap_eq_finrank_range`：finrank_range_dualMap_
eq_finrank_range (f : V₁ ->ₗ[K] V₂) : finrank K (LinearMap.range f.dualMap) = fi
nrank K (LinearMap.range f)
· 使用定理 `Matrix.toLin_eq_toLin'`：Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisF
un R n) (Pi.basisFun R m) = Matrix.toLin'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.toLin'_apply'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type
 u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix
 m n R), M…
· 使用定理 `Matrix.rank.eq_1`：∀ {m : Type um} {n : Type un} {R : Type uR} [inst : Fi
ntype n] [inst_1 : CommSemiring R] (A : Matrix m n R),   A.rank = Module.finrank
 R ↥A.…
-/
theorem rank_transpose [Field R] [Fintype m] (A : Matrix m n R) : Aᵀ.rank = A.rank := by
  classical
  rw [Aᵀ.rank_eq_finrank_range_toLin (Pi.basisFun R n).dualBasis (Pi.basisFun R m).dualBasis,
      toLin_transpose, ← LinearMap.dualMap_def, LinearMap.finrank_range_dualMap_eq_finrank_range,
      toLin_eq_toLin', toLin'_apply', rank]

@[simp]
/-
**Matrix.rank_self_mul_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_self_mul_transpose [Field R] [LinearOrder R] [IsStrictOrderedRing R] 
[Fintype m] (A : Matrix m n R) : (A * Aᵀ).rank = A.rank
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.rank_transpose`：rank_transpose [Field R] [Fintype m] (A : Matrix 
m n R) : Aᵀ.rank = A.rank
· 使用定理 `Matrix.rank_transpose_mul_self`：rank_transpose_mul_self (A : Matrix m n 
R) : (Aᵀ * A).rank = A.rank
-/
theorem rank_self_mul_transpose [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] (A : Matrix m n R) :
    (A * Aᵀ).rank = A.rank := by
  simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ

/-- The rank of a matrix is the rank of the space spanned by its rows. -/
/-
**Matrix.rank_eq_finrank_span_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rank_eq_finrank_span_row [Field R] [Finite m] (A : Matrix m n R) : A.rank 
= finrank R (Submodule.span R (Set.range A.row))
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.rank_transpose`：rank_transpose [Field R] [Fintype m] (A : Matrix 
m n R) : Aᵀ.rank = A.rank
· 使用定理 `Matrix.rank_eq_finrank_span_cols`：rank_eq_finrank_span_cols [CommSemirin
g R] (A : Matrix m n R) : A.rank = finrank R (Submodule.span R (Set.range A.col)
)
· 使用引理 `Matrix.col_transpose`：col_transpose (A : Matrix m n α) : Aᵀ.col = A.row

--- 原说明 ---
The rank of a matrix is the rank of the space spanned by its rows.
-/
theorem rank_eq_finrank_span_row [Field R] [Finite m] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.row)) := by
  cases nonempty_fintype m
  rw [← rank_transpose, rank_eq_finrank_span_cols, col_transpose]
/-
**Matrix._root_.LinearIndependent.rank_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIndependent.rank_matrix [Field R] [Fintype m]
    {M : Matrix m n R} (h : LinearIndependent R M.row) : M.rank = Fintype.card m := by
  rw [M.rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span.mp h, Set.finrank]
/-
**Matrix.rank_add_rank_le_card_of_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`
。
形式化陈述：rank_add_rank_le_card_of_mul_eq_zero [Field R] [Finite l] [Fintype m] {A :
 Matrix l m R} {B : Matrix m n R} (hAB : A * B = 0) : A.rank + B.rank <= Fintype
.card m
参数：hAB : A * B = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.rank_eq_finrank_range_toLin`：rank_eq_finrank_range_toLin [Finite 
m] [DecidableEq n] {M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommM
onoid M₂] [Module R M₁] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma rank_add_rank_le_card_of_mul_eq_zero [Field R] [Finite l] [Fintype m]
    {A : Matrix l m R} {B : Matrix m n R} (hAB : A * B = 0) :
    A.rank + B.rank ≤ Fintype.card m := by
  classical
  let el : Basis l R (l → R) := Pi.basisFun R l
  let em : Basis m R (m → R) := Pi.basisFun R m
  let en : Basis n R (n → R) := Pi.basisFun R n
  rw [Matrix.rank_eq_finrank_range_toLin A el em,
      Matrix.rank_eq_finrank_range_toLin B em en,
      ← Module.finrank_fintype_fun_eq_card R,
      ← LinearMap.finrank_range_add_finrank_ker (Matrix.toLin em el A),
      add_le_add_iff_left]
  apply Submodule.finrank_mono
  rw [LinearMap.range_le_ker_iff, ← Matrix.toLin_mul, hAB, map_zero]

end Matrix

set_option backward.isDefEq.respectTransparency false in
-- TODO: generalize to `cRank` then deprecate
/-
**Matrix.rank_vecMulVec.** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.rank_vecMulVec.{u} {K m n : Type u} [CommRing K] [Fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : (Matrix.vecMulVec w v).toLin'.rank ≤ 1 := by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun', Fintype.card_ofSubsingleton, Nat.cast_one]
