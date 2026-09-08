/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
public import Mathlib.RingTheory.LinearDisjoint

/-!

# Linearly disjoint fields

This file contains basics about the linearly disjoint fields.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean`
and `Mathlib/RingTheory/LinearDisjoint.lean` for details.

## Main definitions

- `IntermediateField.LinearDisjoint`: an intermediate field `A` of `E / F`
  and an abstract field `L` between `E / F`
  (as a special case, two intermediate fields) are linearly disjoint over `F`,
  if they are linearly disjoint as subalgebras (`Subalgebra.LinearDisjoint`).

## Implementation notes

The `Subalgebra.LinearDisjoint` is stated for two `Subalgebra`s. The original design of
`IntermediateField.LinearDisjoint` is also stated for two `IntermediateField`s
(see `IntermediateField.linearDisjoint_iff'` for the original statement).
But it's probably useful if one of them can be generalized to an abstract field
(see <https://github.com/leanprover-community/mathlib4/pull/9651#discussion_r1464070324>).
This leads to the current design of `IntermediateField.LinearDisjoint`
which is for one `IntermediateField` and one abstract field.
It is not generalized to two abstract fields as this will break the dot notation.

## Main results

### Equivalent characterization of linear disjointness

- `IntermediateField.LinearDisjoint.linearIndependent_left`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
  linearly independent over `L`.

- `IntermediateField.LinearDisjoint.of_basis_left`:
  conversely, if there exists an `F`-basis of `A` which remains linearly independent over `L`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_right`:
  `IntermediateField.LinearDisjoint.linearIndependent_right'`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
  linearly independent over `A`.

- `IntermediateField.LinearDisjoint.of_basis_right`:
  `IntermediateField.LinearDisjoint.of_basis_right'`:
  conversely, if there exists an `F`-basis of `L` which remains linearly independent over `A`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_mul`:
  `IntermediateField.LinearDisjoint.linearIndependent_mul'`:
  if `A` and `L` are linearly disjoint, then for any family of
  `F`-linearly independent elements `{ a_i }` of `A`, and any family of
  `F`-linearly independent elements `{ b_j }` of `L`, the family `{ a_i * b_j }` in `S` is
  also `F`-linearly independent.

- `IntermediateField.LinearDisjoint.of_basis_mul`:
  `IntermediateField.LinearDisjoint.of_basis_mul'`:
  conversely, if `{ a_i }` is an `F`-basis of `A`, if `{ b_j }` is an `F`-basis of `L`,
  such that the family `{ a_i * b_j }` in `E` is `F`-linearly independent,
  then `A` and `L` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `IntermediateField.LinearDisjoint.isDomain'`,
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a domain if and only if there exists a field extension of `F` that `A` and `B`
  embed into with linearly disjoint images.

- `IntermediateField.LinearDisjoint.isField_of_forall`,
  `IntermediateField.LinearDisjoint.of_isField'`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a field if and only if for any field extension of `F` that `A` and `B` embed into, their
  images are linearly disjoint.

- `Algebra.TensorProduct.isField_of_isAlgebraic`:
  if `E` and `K` are field extensions of `F`, one of them is algebraic, and
  `E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field.
  See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earlier file).

- `IntermediateField.LinearDisjoint.isField_of_isAlgebraic`,
  `IntermediateField.LinearDisjoint.isField_of_isAlgebraic'`:
  if `A` and `B` are field extensions of `F`, one of them is algebraic, such that they are linearly
  disjoint (more generally, if there exists a field extension of `F` that they embed into with
  linearly disjoint images), then `A ⊗[F] B` is a field.

### Other main results

- `IntermediateField.LinearDisjoint.symm`, `IntermediateField.linearDisjoint_comm`:
  linear disjointness is symmetric.

- `IntermediateField.LinearDisjoint.map`:
  linear disjointness is preserved by algebra homomorphism.

- `IntermediateField.LinearDisjoint.rank_sup`,
  `IntermediateField.LinearDisjoint.finrank_sup`:
  if `A` and `B` are linearly disjoint,
  then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `IntermediateField.LinearDisjoint.of_finrank_sup`:
  conversely, if `A` and `B` are finite extensions,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.of_finrank_coprime`:
  if the rank of `A` and `B` are coprime,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, then they are disjoint.

- `IntermediateField.LinearDisjoint.algEquiv_of_isAlgebraic`:
  linear disjointness is preserved by isomorphisms, provided that one of the field is algebraic.

## Tags

linearly disjoint, linearly independent, tensor product

-/

@[expose] public section

open scoped TensorProduct

open Module IntermediateField

noncomputable section

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/-- If `A` is an intermediate field of `E / F`, and `E / L / F` is a field extension tower,
then `A` and `L` are linearly disjoint, if they are linearly disjoint as subalgebras of `E`
(`Subalgebra.LinearDisjoint`). -/
/-
**IntermediateField.LinearDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`
。
形式化陈述：{F : Type u} →   {E : Type v} →     [inst : Field F] →       [inst_1 : Fie
ld E] →         [inst_2 : Algebra F E] →           IntermediateField F E →      
       (L : Type w) →               [inst_3 : Field L] → [inst_4 : Algebra F L] 
→ [inst_5 : Algebra L E] → [IsScalarTower F L E] → Prop
参数：L : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an intermediate field of `E / F`, and `E / L / F` is a field extension
 tower,
then `A` and `L` are linearly disjoint, if they are linearly disjoint as subalge
bras of `E`
(`Subalgebra.LinearDisjoint`).
-/
protected abbrev LinearDisjoint : Prop :=
  A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range
/-
**IntermediateField.linearDisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：linearDisjoint_iff : A.LinearDisjoint L ↔ A.toSubalgebra.LinearDisjoint (I
sScalarTower.toAlgHom F L E).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearDisjoint_iff :
    A.LinearDisjoint L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range :=
  Iff.rfl

variable {A B L}

/-- Two intermediate fields are linearly disjoint if and only if
they are linearly disjoint as subalgebras. -/
/-
**IntermediateField.linearDisjoint_iff'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：linearDisjoint_iff' : A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B
.toSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.linearDisjoint_iff`：linearDisjoint_iff : A.LinearDisjo
int L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two intermediate fields are linearly disjoint if and only if
they are linearly disjoint as subalgebras.
-/
theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

/-- Linear disjointness is symmetric. -/
/-
**IntermediateField.LinearDisjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield.LinearDisjoint`。
形式化陈述：∀ {F : Type u} {E : Type v} [inst : Field F] [inst_1 : Field E] [inst_2 : 
Algebra F E] {A B : IntermediateField F E},   A.LinearDisjoint ↥B → B.LinearDisj
oint ↥A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Linear disjointness is symmetric.
-/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

/-- Linear disjointness is symmetric. -/
/-
**IntermediateField.linearDisjoint_comm** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.symm`：∀ {F : Type u} {E : Type v} [inst
 : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {A B : IntermediateField F
 E},   A.LinearDisjoint ↥B …

--- 原说明 ---
Linear disjointness is symmetric.
-/
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

section

variable {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]

/-- Linear disjointness is symmetric. -/
/-
**IntermediateField.LinearDisjoint.symm'** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field.LinearDisjoint`。
形式化陈述：∀ {F : Type u} {E : Type v} [inst : Field F] [inst_1 : Field E] [inst_2 : 
Algebra F E] {L : Type w} [inst_3 : Field L]   [inst_4 : Algebra F L] [inst_5 : 
Algebra L E] [inst_6 : IsScalarTower F L E] {L' : Type u_1} [inst_7 : Field L'] 
  [inst_8 : Algebra F L'] [inst_9 : Algebra L' E] [inst_10 : IsScalarTower F L' 
E],   (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L' →     (IsScala
rTower.toAlgHom F L' E).fieldRange.LinearDisjoint L
参数：IsScalarTower.toAlgHom F L E；IsScalarTower.toAlgHom F L' E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {A B : Subalgebra
 R S}, A.LinearDisjo…

--- 原说明 ---
Linear disjointness is symmetric.
-/
theorem LinearDisjoint.symm' (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L') :
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.symm H

/-- Linear disjointness is symmetric. -/
/-
**IntermediateField.linearDisjoint_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：linearDisjoint_comm' : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDis
joint L' ↔ (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.symm'`：∀ {F : Type u} {E : Type v} [ins
t : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {L : Type w} [inst_3 : Fi
eld L]   [inst_4 : Algebra F…

--- 原说明 ---
Linear disjointness is symmetric.
-/
theorem linearDisjoint_comm' :
    (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L' ↔
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  ⟨LinearDisjoint.symm', LinearDisjoint.symm'⟩

end

namespace LinearDisjoint

/-- Linear disjointness of intermediate fields is preserved by algebra homomorphisms. -/
/-
**IntermediateField.LinearDisjoint.map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld.LinearDisjoint`。
形式化陈述：map (H : A.LinearDisjoint B) {K : Type*} [Field K] [Algebra F K] (f : E ->
ₐ[F] K) : (A.map f).LinearDisjoint (B.map f)
参数：H : A.LinearDisjoint B；f : E ->ₐ[F] K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.map`：map (H : A.LinearDisjoint B) {T : Type w}
 [Semiring T] [Algebra R T] (f : S ->ₐ[R] T) (hf : Function.Injective f) : (A.ma
p f).LinearDisjoint…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
Linear disjointness of intermediate fields is preserved by algebra homomorphisms
.
-/
theorem map (H : A.LinearDisjoint B) {K : Type*} [Field K] [Algebra F K]
    (f : E →ₐ[F] K) : (A.map f).LinearDisjoint (B.map f) :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).map f f.injective)

/-- Linear disjointness of an intermediate field with a tower of field embeddings is preserved by
algebra homomorphisms. -/
/-
**IntermediateField.LinearDisjoint.map'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield.LinearDisjoint`。
形式化陈述：map' (H : A.LinearDisjoint L) (K : Type*) [Field K] [Algebra F K] [Algebra
 L K] [IsScalarTower F L K] [Algebra E K] [IsScalarTower F E K] [IsScalarTower L
 E K] : (A.map (IsScalarTower.toAlgHom F E K)).LinearDisjoint L
参数：H : A.LinearDisjoint L；K : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.linearDisjoint_iff`：linearDisjoint_iff : A.LinearDisjo
int L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range
· 使用定理 `Subalgebra.LinearDisjoint.map`：map (H : A.LinearDisjoint B) {T : Type w}
 [Semiring T] [Algebra R T] (f : S ->ₐ[R] T) (hf : Function.Injective f) : (A.ma
p f).LinearDisjoint…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `AlgHom.range_comp`：range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.com
p f).range = f.range.map g

--- 原说明 ---
Linear disjointness of an intermediate field with a tower of field embeddings is
 preserved by
algebra homomorphisms.
-/
theorem map' (H : A.LinearDisjoint L) (K : Type*) [Field K] [Algebra F K] [Algebra L K]
    [IsScalarTower F L K] [Algebra E K] [IsScalarTower F E K] [IsScalarTower L E K] :
    (A.map (IsScalarTower.toAlgHom F E K)).LinearDisjoint L := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  rw [← AlgHom.range_comp] at this
  convert! this
  ext; exact IsScalarTower.algebraMap_apply L E K _

/-- Linear disjointness is preserved by algebra homomorphism. -/
/-
**IntermediateField.LinearDisjoint.map''** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field.LinearDisjoint`。
形式化陈述：map'' {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower
 F L' E] (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L') (K : 
Type*) [Field K] [Algebra F K] [Algebra L K] [IsScalarTower F L K] [Algebra L' K
] [IsScalarTower F L' K] [Algebra E K] [IsScalarTower F E K] [IsScalarTower L E 
K] [IsScalarTower L' E K] : (IsScalarTower.toAlgHom F L K).fieldRange.LinearDisj
oint L'
参数：H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L'；K : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.linearDisjoint_iff`：linearDisjoint_iff : A.LinearDisjo
int L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range
· 使用定理 `Subalgebra.LinearDisjoint.map`：map (H : A.LinearDisjoint B) {T : Type w}
 [Semiring T] [Algebra R T] (f : S ->ₐ[R] T) (hf : Function.Injective f) : (A.ma
p f).LinearDisjoint…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgHom.fieldRange_toSubalgebra`：∀ {K : Type u_1} {L : Type u_2} {L' : Ty
pe u_3} [inst : Field K] [inst_1 : Field L] [inst_2 : Field L']   [inst_3 : Alge
bra K L] [inst_4 : A…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Linear disjointness is preserved by algebra homomorphism.
-/
theorem map'' {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]
    (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L')
    (K : Type*) [Field K] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra L' K] [IsScalarTower F L' K] [Algebra E K] [IsScalarTower F E K]
    [IsScalarTower L E K] [IsScalarTower L' E K] :
    (IsScalarTower.toAlgHom F L K).fieldRange.LinearDisjoint L' := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  simp_rw [AlgHom.fieldRange_toSubalgebra, ← AlgHom.range_comp] at this
  rw [AlgHom.fieldRange_toSubalgebra]
  convert! this <;> (ext; exact IsScalarTower.algebraMap_apply _ E K _)

variable (A) in
/-
**IntermediateField.LinearDisjoint.self_right** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField.LinearDisjoint`。
形式化陈述：self_right : A.LinearDisjoint F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.bot_right`：bot_right : A.LinearDisjoint ⊥
-/
theorem self_right : A.LinearDisjoint F := Subalgebra.LinearDisjoint.bot_right _

variable (A) in
/-
**IntermediateField.LinearDisjoint.bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField.LinearDisjoint`。
形式化陈述：bot_right : A.LinearDisjoint (⊥ : IntermediateField F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.bot_right`：bot_right : A.LinearDisjoint ⊥
-/
theorem bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)

variable (F E L) in
/-
**IntermediateField.LinearDisjoint.bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField.LinearDisjoint`。
形式化陈述：bot_left : (⊥ : IntermediateField F E).LinearDisjoint L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.bot_left`：bot_left : (⊥ : Subalgebra R S).Line
arDisjoint B
-/
theorem bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  Subalgebra.LinearDisjoint.bot_left _

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
linearly independent over `L`. -/
/-
**IntermediateField.LinearDisjoint.linearIndependent_left** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：linearIndependent_left (H : A.LinearDisjoint L) {ι : Type*} {a : ι -> A} (
ha : LinearIndependent F a) : LinearIndependent L (A.val ∘ a)
参数：H : A.LinearDisjoint L；ha : LinearIndependent F a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.map_of_injective_injective`：LinearIndependent.map_of_i
njective_injective {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M'] (h
v : LinearIndependent R v) (i : R'…
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`：linearIndepend
ent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B] {ι : Type*} {a : ι -
> A} (ha : LinearIndependent R a) : LinearInde…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x

--- 原说明 ---
If `A` and `L` are linearly disjoint, then any `F`-linearly independent family o
n `A` remains
linearly independent over `L`.
-/
theorem linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι → A} (ha : LinearIndependent F a) : LinearIndependent L (A.val ∘ a) :=
  (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If there exists an `F`-basis of `A` which remains linearly independent over `L`, then
`A` and `L` are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_basis_left** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField.LinearDisjoint`。
形式化陈述：of_basis_left {ι : Type*} (a : Basis ι F A) (H : LinearIndependent L (A.va
l ∘ a)) : A.LinearDisjoint L
参数：a : Basis ι F A；H : LinearIndependent L (A.val ∘ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_left`：of_basis_left {ι : Type*} (a : 
Basis ι R A) (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B
· 使用定理 `LinearIndependent.map_of_surjective_injective`：LinearIndependent.map_of_
surjective_injective {R' M' : Type*} [Semiring R'] [AddCommMonoid M'] [Module R'
 M'] (hv : LinearIndependent R v) (…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x

--- 原说明 ---
If there exists an `F`-basis of `A` which remains linearly independent over `L`,
 then
`A` and `L` are linearly disjoint.
-/
theorem of_basis_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_left _ _ a <| H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `B` remains
linearly independent over `A`. -/
/-
**IntermediateField.LinearDisjoint.linearIndependent_right** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：linearIndependent_right (H : A.LinearDisjoint B) {ι : Type*} {b : ι -> B} 
(hb : LinearIndependent F b) : LinearIndependent A (B.val ∘ b)
参数：H : A.LinearDisjoint B；hb : LinearIndependent F b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`：linearIndepen
dent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A] {ι : Type*} {b : ι
 -> B} (hb : LinearIndependent R b) : LinearInd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
If `A` and `B` are linearly disjoint, then any `F`-linearly independent family o
n `B` remains
linearly independent over `A`.
-/
theorem linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι → B} (hb : LinearIndependent F b) : LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb

/--
If `A` and `B` are linearly disjoint and such that `A.toSubalgebra ⊔ B.toSubalgebra = ⊤`,
then any `F`-basis of `B` is also an `A`-basis of `E`.
Note that the condition `A.toSubalgebra ⊔ B.toSubalgebra = ⊤` is equivalent to
`A ⊔ B = ⊤` in many cases, see `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right` and similar
results.
-/
/-
**IntermediateField.LinearDisjoint.basisOfBasisRight** 是 Mathlib 中的一个定义，位于命名空间 `
IntermediateField.LinearDisjoint`。
形式化陈述：basisOfBasisRight (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSuba
lgebra = ⊤) {ι : Type*} (b : Basis ι F B) : Basis ι A E
参数：H : A.LinearDisjoint B；H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤；b : Basis ι F
 B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are linearly disjoint and such that `A.toSubalgebra ⊔ B.toSubalge
bra = ⊤`,
then any `F`-basis of `B` is also an `A`-basis of `E`.
Note that the condition `A.toSubalgebra ⊔ B.toSubalgebra = ⊤` is equivalent to
`A ⊔ B = ⊤` in many cases, see `IntermediateField.sup_toSubalgebra_of_isAlgebrai
c_right` and similar
results.
-/
noncomputable def basisOfBasisRight (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) :
    Basis ι A E :=
  (linearDisjoint_iff'.mp H).basisOfBasisRight H' b

@[simp]
/-
**IntermediateField.LinearDisjoint.basisOfBasisRight_apply** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：basisOfBasisRight_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.
toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) (i : ι) : H.basisOfBasisRight H'
 b i = algebraMap B E (b i)
参数：H : A.LinearDisjoint B；H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤；b : Basis ι F
 B；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_apply`：algebraMap
_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι) 
: H.basisOfBasisRight H' b i = algebraMap B S (b i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
-/
theorem basisOfBasisRight_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
    {ι : Type*} (b : Basis ι F B) (i : ι) :
    H.basisOfBasisRight H' b i = algebraMap B E (b i) :=
  (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_apply H' b i
/-
**IntermediateField.LinearDisjoint.algebraMap_basisOfBasisRight_repr_apply** 是 M
athlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：algebraMap_basisOfBasisRight_repr_apply (H : A.LinearDisjoint B) (H' : A.t
oSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) (x : B) (i : ι) 
: algebraMap A E ((H.basisOfBasisRight H' b).repr x i) = algebraMap F E (b.repr 
x i)
参数：H : A.LinearDisjoint B；H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤；b : Basis ι F
 B；x : B；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.algebraMap_basisOfBasisRight_repr_apply`：algeb
raMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B
) (x : B) (i : ι) : algebraMap A S ((H.basisOfBasisRigh…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
-/
theorem algebraMap_basisOfBasisRight_repr_apply (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) (x : B) (i : ι) :
    algebraMap A E ((H.basisOfBasisRight H' b).repr x i) = algebraMap F E (b.repr x i) :=
  (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_repr_apply H' b x i

/--
If `A` and `B` are linearly disjoint and such that `A.toSubalgebra ⊔ B.toSubalgebra = ⊤`,
then any `F`-basis of `A` is also a `B`-basis of `E`.
Note that the condition `A.toSubalgebra ⊔ B.toSubalgebra = ⊤` is equivalent to
`A ⊔ B = ⊤` in many cases, see `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right` and similar
results.
-/
/-
**IntermediateField.LinearDisjoint.basisOfBasisLeft** 是 Mathlib 中的一个定义，位于命名空间 `I
ntermediateField.LinearDisjoint`。
形式化陈述：basisOfBasisLeft (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubal
gebra = ⊤) {ι : Type*} (b : Basis ι F A) : Basis ι B E
参数：H : A.LinearDisjoint B；H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤；b : Basis ι F
 A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are linearly disjoint and such that `A.toSubalgebra ⊔ B.toSubalge
bra = ⊤`,
then any `F`-basis of `A` is also a `B`-basis of `E`.
Note that the condition `A.toSubalgebra ⊔ B.toSubalgebra = ⊤` is equivalent to
`A ⊔ B = ⊤` in many cases, see `IntermediateField.sup_toSubalgebra_of_isAlgebrai
c_right` and similar
results.
-/
noncomputable def basisOfBasisLeft (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) :
    Basis ι B E :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft H' b

@[simp]
/-
**IntermediateField.LinearDisjoint.basisOfBasisLeft_apply** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：basisOfBasisLeft_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.t
oSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) (i : ι) : H.basisOfBasisLeft H' b
 i = algebraMap A E (b i)
参数：H : A.LinearDisjoint B；H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤；b : Basis ι F
 A；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.basisOfBasisLeft_apply`：basisOfBasisLeft_apply
 (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (i : ι) : H.basisOfBasisLeft H' 
b i = algebraMap A S (b i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
-/
theorem basisOfBasisLeft_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
    {ι : Type*} (b : Basis ι F A) (i : ι) :
    H.basisOfBasisLeft H' b i = algebraMap A E (b i) :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft_apply H' b i
/-
**IntermediateField.LinearDisjoint.basisOfBasisLeft_repr_apply** 是 Mathlib 中的一个定
理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：basisOfBasisLeft_repr_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra 
⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) (x : A) (i : ι) : algebraMap
 B E ((H.basisOfBasisLeft H' b).repr x i) = algebraMap F E (b.repr x i)
参数：H : A.LinearDisjoint B；H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤；b : Basis ι F
 A；x : A；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.basisOfBasisLeft_repr_apply`：basisOfBasisLeft_
repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (x : A) (i : ι) : alge
braMap B S ((H.basisOfBasisLeft H' b).repr …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
-/
theorem basisOfBasisLeft_repr_apply (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) (x : A) (i : ι) :
    algebraMap B E ((H.basisOfBasisLeft H' b).repr x i) = algebraMap F E (b.repr x i) :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft_repr_apply H' b x i

/-- If there exists an `F`-basis of `B` which remains linearly independent over `A`, then
`A` and `B` are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_basis_right** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField.LinearDisjoint`。
形式化陈述：of_basis_right {ι : Type*} (b : Basis ι F B) (H : LinearIndependent A (B.v
al ∘ b)) : A.LinearDisjoint B
参数：b : Basis ι F B；H : LinearIndependent A (B.val ∘ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_right`：of_basis_right {ι : Type*} (b 
: Basis ι R B) (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B

--- 原说明 ---
If there exists an `F`-basis of `B` which remains linearly independent over `A`,
 then
`A` and `B` are linearly disjoint.
-/
theorem of_basis_right {ι : Type*} (b : Basis ι F B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_right _ _ b H)

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
linearly independent over `A`. -/
/-
**IntermediateField.LinearDisjoint.linearIndependent_right'** 是 Mathlib 中的一个定理，位
于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：linearIndependent_right' (H : A.LinearDisjoint L) {ι : Type*} {b : ι -> L}
 (hb : LinearIndependent F b) : LinearIndependent A (algebraMap L E ∘ b)
参数：H : A.LinearDisjoint L；hb : LinearIndependent F b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`：linearIndepen
dent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A] {ι : Type*} {b : ι
 -> B} (hb : LinearIndependent R b) : LinearInd…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…

--- 原说明 ---
If `A` and `L` are linearly disjoint, then any `F`-linearly independent family o
n `L` remains
linearly independent over `A`.
-/
theorem linearIndependent_right' (H : A.LinearDisjoint L) {ι : Type*} {b : ι → L}
    (hb : LinearIndependent F b) : LinearIndependent A (algebraMap L E ∘ b) := by
  apply Subalgebra.LinearDisjoint.linearIndependent_right_of_flat H <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

/-- If there exists an `F`-basis of `L` which remains linearly independent over `A`, then
`A` and `L` are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_basis_right'** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField.LinearDisjoint`。
形式化陈述：of_basis_right' {ι : Type*} (b : Basis ι F L) (H : LinearIndependent A (al
gebraMap L E ∘ b)) : A.LinearDisjoint L
参数：b : Basis ι F L；H : LinearIndependent A (algebraMap L E ∘ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_right`：of_basis_right {ι : Type*} (b 
: Basis ι R B) (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If there exists an `F`-basis of `L` which remains linearly independent over `A`,
 then
`A` and `L` are linearly disjoint.
-/
theorem of_basis_right' {ι : Type*} (b : Basis ι F L)
    (H : LinearIndependent A (algebraMap L E ∘ b)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

/-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
/-
**IntermediateField.LinearDisjoint.linearIndependent_mul** 是 Mathlib 中的一个定理，位于命名
空间 `IntermediateField.LinearDisjoint`。
形式化陈述：linearIndependent_mul (H : A.LinearDisjoint B) {κ ι : Type*} {a : κ -> A} 
{b : ι -> B} (ha : LinearIndependent F a) (hb : LinearIndependent F b) : LinearI
ndependent F fun (i : κ × ι) => (a i.1).1 * (b i.2).1
参数：H : A.LinearDisjoint B；ha : LinearIndependent F a；hb : LinearIndependent F b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left`：linearInde
pendent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A] {κ ι : Type*
} {a : κ -> A} {b : ι -> B} (ha : LinearIndependen…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
If `A` and `B` are linearly disjoint, then for any `F`-linearly independent fami
lies
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
are linearly independent over `F`.
-/
theorem linearIndependent_mul (H : A.LinearDisjoint B) {κ ι : Type*} {a : κ → A} {b : ι → B}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  (linearDisjoint_iff'.1 H).linearIndependent_mul_of_flat_left ha hb

/-- If `A` and `L` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `L`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
/-
**IntermediateField.LinearDisjoint.linearIndependent_mul'** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：linearIndependent_mul' (H : A.LinearDisjoint L) {κ ι : Type*} {a : κ -> A}
 {b : ι -> L} (ha : LinearIndependent F a) (hb : LinearIndependent F b) : Linear
Independent F fun (i : κ × ι) => (a i.1).1 * algebraMap L E (b i.2)
参数：H : A.LinearDisjoint L；ha : LinearIndependent F a；hb : LinearIndependent F b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left`：linearInde
pendent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A] {κ ι : Type*
} {a : κ -> A} {b : ι -> B} (ha : LinearIndependen…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…

--- 原说明 ---
If `A` and `L` are linearly disjoint, then for any `F`-linearly independent fami
lies
`{ u_i }`, `{ v_j }` of `A`, `L`, the products `{ u_i * v_j }`
are linearly independent over `F`.
-/
theorem linearIndependent_mul' (H : A.LinearDisjoint L) {κ ι : Type*} {a : κ → A} {b : ι → L}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2) := by
  apply Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left H ha <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_basis_mul** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField.LinearDisjoint`。
形式化陈述：of_basis_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B) (H : Linear
Independent F fun (i : κ × ι) => (a i.1).1 * (b i.2).1) : A.LinearDisjoint B
参数：a : Basis κ F A；b : Basis ι F B；H : LinearIndependent F fun (i : κ × ι) => (a
 i.1).1 * (b i.2).1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_mul`：of_basis_mul {κ ι : Type*} (a : 
Basis κ R A) (b : Basis ι R B) (H : LinearIndependent R fun (i : κ × ι) => (a i.
1).1 * (b i.2).1) : A.Linear…

--- 原说明 ---
If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly
 disjoint.
-/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_mul _ _ a b H)

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `L`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `L` are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_basis_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField.LinearDisjoint`。
形式化陈述：of_basis_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L) (H : Linea
rIndependent F fun (i : κ × ι) => (a i.1).1 * algebraMap L E (b i.2)) : A.Linear
Disjoint L
参数：a : Basis κ F A；b : Basis ι F L；H : LinearIndependent F fun (i : κ × ι) => (a
 i.1).1 * algebraMap L E (b i.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_basis_mul`：of_basis_mul {κ ι : Type*} (a : 
Basis κ R A) (b : Basis ι R B) (H : LinearIndependent R fun (i : κ × ι) => (a i.
1).1 * (b i.2).1) : A.Linear…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `L`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `L` are linearly
 disjoint.
-/
theorem of_basis_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2)) :
    A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H
/-
**IntermediateField.LinearDisjoint.of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField.LinearDisjoint`。
形式化陈述：of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L) (h : A' <
= A) : A'.LinearDisjoint L
参数：H : A.LinearDisjoint L；h : A' <= A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat {A' : S
ubalgebra R S} (h : A' <= A) [Module.Flat R B] : A'.LinearDisjoint B
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (h : A' ≤ A) : A'.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_le_left_of_flat H h
/-
**IntermediateField.LinearDisjoint.of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField.LinearDisjoint`。
形式化陈述：of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B) (h : B' 
<= B) : A.LinearDisjoint B'
参数：H : A.LinearDisjoint B；h : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat {B' :
 Subalgebra R S} (h : B' <= B) [Module.Flat R A] : A.LinearDisjoint B'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' ≤ B) : A.LinearDisjoint B' :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

/-- Similar to `IntermediateField.LinearDisjoint.of_le_right` but this is for abstract fields. -/
/-
**IntermediateField.LinearDisjoint.of_le_right'** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField.LinearDisjoint`。
形式化陈述：of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L'] [Algebra F L
'] [Algebra L' L] [IsScalarTower F L' L] [Algebra L' E] [IsScalarTower F L' E] [
IsScalarTower L' L E] : A.LinearDisjoint L'
参数：H : A.LinearDisjoint L；L' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat {B' :
 Subalgebra R S} (h : B' <= B) [Module.Flat R A] : A.LinearDisjoint B'
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `AlgHom.range_comp_le_range`：range_comp_le_range (f : A ->ₐ[R] B) (g : B 
->ₐ[R] C) : (g.comp f).range <= g.range
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
Similar to `IntermediateField.LinearDisjoint.of_le_right` but this is for abstra
ct fields.
-/
theorem of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A.LinearDisjoint L' := by
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat H ?_
  convert! AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext; exact IsScalarTower.algebraMap_apply L' L E _

/-- If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`,
respectively, then `A'` and `B'` are also linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field.LinearDisjoint`。
形式化陈述：of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B) (hA : A' <=
 A) (hB : B' <= B) : A'.LinearDisjoint B'
参数：H : A.LinearDisjoint B；hA : A' <= A；hB : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.of_le_right`：of_le_right {B' : Intermed
iateField F E} (H : A.LinearDisjoint B) (h : B' <= B) : A.LinearDisjoint B'
· 使用定理 `IntermediateField.LinearDisjoint.of_le_left`：of_le_left {A' : Intermedia
teField F E} (H : A.LinearDisjoint L) (h : A' <= A) : A'.LinearDisjoint L

--- 原说明 ---
If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`
,
respectively, then `A'` and `B'` are also linearly disjoint.
-/
theorem of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
  H.of_le_left hA |>.of_le_right hB

/-- Similar to `IntermediateField.LinearDisjoint.of_le` but this is for abstract fields. -/
/-
**IntermediateField.LinearDisjoint.of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField.LinearDisjoint`。
形式化陈述：of_le' {A' : IntermediateField F E} (H : A.LinearDisjoint L) (hA : A' <= A
) (L' : Type*) [Field L'] [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L] [
Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A'.LinearDisjoint 
L'
参数：H : A.LinearDisjoint L；hA : A' <= A；L' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.of_le_right'`：of_le_right' (H : A.Linea
rDisjoint L) (L' : Type*) [Field L'] [Algebra F L'] [Algebra L' L] [IsScalarTowe
r F L' L] [Algebra L' E] [IsScalarT…
· 使用定理 `IntermediateField.LinearDisjoint.of_le_left`：of_le_left {A' : Intermedia
teField F E} (H : A.LinearDisjoint L) (h : A' <= A) : A'.LinearDisjoint L

--- 原说明 ---
Similar to `IntermediateField.LinearDisjoint.of_le` but this is for abstract fie
lds.
-/
theorem of_le' {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (hA : A' ≤ A) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A'.LinearDisjoint L' :=
  H.of_le_left hA |>.of_le_right' L'

/--
If `A` and `B` are linearly disjoint over `F`, then their intersection is equal to `F`.
This is actually an equivalence if `A/F` and `B/F` are finite dimensional, and `A/F` is Galois,
see `IntermediateField.LinearDisjoint.iff_inf_eq_bot`.
-/
/-
**IntermediateField.LinearDisjoint.inf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField.LinearDisjoint`。
形式化陈述：inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥
参数：H : A.LinearDisjoint B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `Subalgebra.LinearDisjoint.inf_eq_bot`：inf_eq_bot (H : A.LinearDisjoint B
) : A ⊓ B = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra

--- 原说明 ---
If `A` and `B` are linearly disjoint over `F`, then their intersection is equal 
to `F`.
This is actually an equivalence if `A/F` and `B/F` are finite dimensional, and `
A/F` is Galois,
see `IntermediateField.LinearDisjoint.iff_inf_eq_bot`.
-/
theorem inf_eq_bot (H : A.LinearDisjoint B) :
    A ⊓ B = ⊥ := toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot

/-- If `A` and `A` itself are linearly disjoint over `F`, then it is equal to `F`. -/
/-
**IntermediateField.LinearDisjoint.eq_bot_of_self** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField.LinearDisjoint`。
形式化陈述：eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥
参数：H : A.LinearDisjoint A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.inf_eq_bot`：inf_eq_bot (H : A.LinearDis
joint B) : A ⊓ B = ⊥
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a

--- 原说明 ---
If `A` and `A` itself are linearly disjoint over `F`, then it is equal to `F`.
-/
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  inf_idem A ▸ H.inf_eq_bot

/-- If `A` and `B` are linearly disjoint over `F`, then the
rank of `A ⊔ B` is equal to the product of that of `A` and `B`. -/
/-
**IntermediateField.LinearDisjoint.rank_sup** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField.LinearDisjoint`。
形式化陈述：rank_sup (H : A.LinearDisjoint B) : Module.rank F ↥(A ⊔ B) = Module.rank F
 A * Module.rank F B
参数：H : A.LinearDisjoint B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.le_sup_toSubalgebra`：le_sup_toSubalgebra : E1.toSubalg
ebra ⊔ E2.toSubalgebra <= (E1 ⊔ E2).toSubalgebra
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IntermediateField.rank_sup_le`：IntermediateField.rank_sup_le {F : Type u
} {E : Type v} [Field F] [Field E] [Algebra F E] (A B : IntermediateField F E) :
 Module.rank F ↥(A …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subalgebra.LinearDisjoint.rank_sup_of_free`：rank_sup_of_free [Module.Fre
e R A] [Module.Free R B] : Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.ran
k R B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)

--- 原说明 ---
If `A` and `B` are linearly disjoint over `F`, then the
rank of `A ⊔ B` is equal to the product of that of `A` and `B`.
-/
theorem rank_sup (H : A.LinearDisjoint B) :
    Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B :=
  have h := le_sup_toSubalgebra A B
  (rank_sup_le A B).antisymm <|
    (linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans <|
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

/-- If `A` and `B` are linearly disjoint over `F`, then the `Module.finrank` of
`A ⊔ B` is equal to the product of that of `A` and `B`. -/
/-
**IntermediateField.LinearDisjoint.finrank_sup** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField.LinearDisjoint`。
形式化陈述：finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * 
finrank F B
参数：H : A.LinearDisjoint B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.LinearDisjoint.rank_sup`：rank_sup (H : A.LinearDisjoin
t B) : Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B

--- 原说明 ---
If `A` and `B` are linearly disjoint over `F`, then the `Module.finrank` of
`A ⊔ B` is equal to the product of that of `A` and `B`.
-/
theorem finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup))

/-- If `A` and `B` are finite extensions of `F`,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_finrank_sup** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField.LinearDisjoint`。
形式化陈述：of_finrank_sup [FiniteDimensional F A] [FiniteDimensional F B] (H : finran
k F ↥(A ⊔ B) = finrank F A * finrank F B) : A.LinearDisjoint B
参数：H : finrank F ↥(A ⊔ B) = finrank F A * finrank F B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.of_finrank_sup_of_free`：of_finrank_sup_of_free
 [Module.Free R A] [Module.Free R B] [Module.Finite R A] [Module.Finite R B] (H 
: Module.finrank R ↥(A ⊔ B) = Module.f…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.sup_toSubalgebra_of_left`：sup_toSubalgebra_of_left [Fi
niteDimensional K E1] : (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgeb
ra

--- 原说明 ---
If `A` and `B` are finite extensions of `F`,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint.
-/
theorem of_finrank_sup [FiniteDimensional F A] [FiniteDimensional F B]
    (H : finrank F ↥(A ⊔ B) = finrank F A * finrank F B) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 <| .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])

/-- If `A` and `B` are linearly disjoint over `F` and `A ⊔ B = E`, then the `Module.finrank` of
`E` over `A` is equal to the `Module.finrank` of `B` over `F`.
-/
/-
**IntermediateField.LinearDisjoint.finrank_left_eq_finrank** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：finrank_left_eq_finrank [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ 
: A ⊔ B = ⊤) : finrank A E = finrank F B
参数：h₁ : A.LinearDisjoint B；h₂ : A ⊔ B = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.finrank_sup`：finrank_sup (H : A.LinearD
isjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IntermediateField.finrank_top'`：∀ {F : Type u_1} [inst : Field F] {E : T
ype u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.finrank F ↥⊤ = Modu
le.finrank F E

--- 原说明 ---
If `A` and `B` are linearly disjoint over `F` and `A ⊔ B = E`, then the `Module.
finrank` of
`E` over `A` is equal to the `Module.finrank` of `B` over `F`.
-/
theorem finrank_left_eq_finrank [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) :
    finrank A E = finrank F B := by
  have := h₁.finrank_sup
  rwa [h₂, finrank_top', ← finrank_mul_finrank F A E, mul_right_inj' finrank_pos.ne'] at this

/-- If `A` and `B` are linearly disjoint over `F` and `A ⊔ B = E`, then the `Module.finrank` of
`E` over `B` is equal to the `Module.finrank` of `A` over `F`.
-/
/-
**IntermediateField.LinearDisjoint.finrank_right_eq_finrank** 是 Mathlib 中的一个定理，位
于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：finrank_right_eq_finrank [Module.Finite F B] (h₁ : A.LinearDisjoint B) (h₂
 : A ⊔ B = ⊤) : finrank B E = finrank F A
参数：h₁ : A.LinearDisjoint B；h₂ : A ⊔ B = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.finrank_left_eq_finrank`：finrank_left_e
q_finrank [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) : finra
nk A E = finrank F B
· 使用定理 `IntermediateField.LinearDisjoint.symm`：∀ {F : Type u} {E : Type v} [inst
 : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {A B : IntermediateField F
 E},   A.LinearDisjoint ↥B …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a

--- 原说明 ---
If `A` and `B` are linearly disjoint over `F` and `A ⊔ B = E`, then the `Module.
finrank` of
`E` over `B` is equal to the `Module.finrank` of `A` over `F`.
-/
theorem finrank_right_eq_finrank [Module.Finite F B] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) :
    finrank B E = finrank F A :=
  h₁.symm.finrank_left_eq_finrank (by rwa [sup_comm])
/-
**IntermediateField.LinearDisjoint.of_inf_eq_bot_aux** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField.LinearDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem of_inf_eq_bot_aux [IsGalois F A] [FiniteDimensional F E] (h₁ : A ⊔ B = ⊤)
    (h₂ : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  apply LinearDisjoint.of_finrank_sup
  rw [h₁, finrank_top', ← Module.finrank_mul_finrank F B E, mul_comm, mul_left_inj'
    Module.finrank_pos.ne']
  have : IsGalois B E := IsGalois.sup_right A B h₁
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr <| Equiv.ofBijective (restrictRestrictAlgEquivMapHom _ _ _ _)
    ⟨restrictRestrictAlgEquivMapHom_injective _ _ h₁,
      restrictRestrictAlgEquivMapHom_surjective _ _ h₂⟩

/--
If `A` and `B` are finite extensions of `F`, with `A/F` Galois, such that `A ⊓ B = F`, then
`A` and `B` are linearly disjoint over `F`.
-/
/-
**IntermediateField.LinearDisjoint.of_inf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField.LinearDisjoint`。
形式化陈述：of_inf_eq_bot [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F 
B] (h : A ⊓ B = ⊥) : A.LinearDisjoint B
参数：h : A ⊓ B = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `IntermediateField.lift_restrict`：lift_restrict : lift (restrict h) = F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.lift_inj`：lift_inj {F : IntermediateField K L} (E E' :
 IntermediateField K F) : lift E = lift E' ↔ E = E'
· 使用定理 `IntermediateField.lift_top`：lift_top (K : IntermediateField F E) : lift 
(F
· 使用定理 `IntermediateField.lift_sup`：lift_sup (K : IntermediateField F E) (L L' :
 IntermediateField F K) : lift (L ⊔ L') = lift L ⊔ lift L'
· 使用定理 `IntermediateField.lift_bot`：lift_bot (K : IntermediateField F E) : lift 
(F
· 使用定理 `IntermediateField.lift_inf`：lift_inf (K : IntermediateField F E) (L L' :
 IntermediateField F K) : lift (L ⊓ L') = lift L ⊓ lift L'
· 使用定理 `IsGalois.of_algEquiv`：IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E
') : IsGalois F E'
· 使用定理 `_private.Mathlib.FieldTheory.LinearDisjoint.0.IntermediateField.LinearDi
sjoint.of_inf_eq_bot_aux`：∀ {F : Type u} {E : Type v} [inst : Field F] [inst_1 :
 Field E] [inst_2 : Algebra F E] {A B : IntermediateField F E}   [IsGalois F ↥A]
 [Fini…
· 使用定理 `IntermediateField.LinearDisjoint.map`：map (H : A.LinearDisjoint B) {K : 
Type*} [Field K] [Algebra F K] (f : E ->ₐ[F] K) : (A.map f).LinearDisjoint (B.ma
p f)

--- 原说明 ---
If `A` and `B` are finite extensions of `F`, with `A/F` Galois, such that `A ⊓ B
 = F`, then
`A` and `B` are linearly disjoint over `F`.
-/
theorem of_inf_eq_bot [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
    (h : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  let C : IntermediateField F E := A ⊔ B
  let A' : IntermediateField F C := A.restrict le_sup_left
  let B' : IntermediateField F C := B.restrict le_sup_right
  have hA : IntermediateField.map C.val A' = A := lift_restrict le_sup_left
  have hB : IntermediateField.map C.val B' = B := lift_restrict le_sup_right
  suffices A'.LinearDisjoint B' from hA ▸ hB ▸ LinearDisjoint.map this C.val
  have h₁ : A' ⊔ B' = ⊤ := by
    rw [← lift_inj, lift_top, lift_sup, lift_restrict le_sup_left, lift_restrict le_sup_right]
  have h₂ : A' ⊓ B' = ⊥ := by
    rw [← lift_inj, lift_bot, lift_inf, lift_restrict le_sup_left, lift_restrict le_sup_right, h]
  have : IsGalois F A' := IsGalois.of_algEquiv <| restrictAlgEquiv ..
  exact of_inf_eq_bot_aux h₁ h₂

@[simp]
/-
**IntermediateField.LinearDisjoint.iff_inf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField.LinearDisjoint`。
形式化陈述：iff_inf_eq_bot [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F
 B] : A.LinearDisjoint B ↔ A ⊓ B = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.inf_eq_bot`：inf_eq_bot (H : A.LinearDis
joint B) : A ⊓ B = ⊥
· 使用定理 `IntermediateField.LinearDisjoint.of_inf_eq_bot`：of_inf_eq_bot [IsGalois 
F A] [FiniteDimensional F A] [FiniteDimensional F B] (h : A ⊓ B = ⊥) : A.LinearD
isjoint B
-/
theorem iff_inf_eq_bot [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B] :
    A.LinearDisjoint B ↔ A ⊓ B = ⊥ :=
  ⟨fun h ↦ inf_eq_bot h, fun h ↦ of_inf_eq_bot h⟩

/-- If `A` and `L` are linearly disjoint over `F`, one of them is algebraic,
then `[L(A) : L] = [A : F]`. -/
/-
**IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic** 是 M
athlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_left_of_isAlgebraic (H : A.LinearDisjoint L) (halg : A
lgebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank L (adjoin L (A :
 Set E)) = Module.rank F A
参数：H : A.LinearDisjoint L；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F
 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic`：
adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
 (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) …
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Algebra.adjoin_toSubsemiring`：∀ (R : Type u) {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set A),   (Algebra.a
djoin R s).toSubse…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `rank_eq_of_equiv_equiv`：rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M
₁) (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) : Mod
ule.rank R M…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left`：adjoin_rank_eq_rank_
left [Module.Free R A] [Module.Flat R B] [Nontrivial R] [Nontrivial S] : Module.
rank B (Algebra.adjoin B (A : Set S)) = …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A

--- 原说明 ---
If `A` and `L` are linearly disjoint over `F`, one of them is algebraic,
then `[L(A) : L] = [A : F]`.
-/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank L (adjoin L (A : Set E)) = Module.rank F A := by
  refine Eq.trans ?_ (Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left H)
  set L' := (IsScalarTower.toAlgHom F L E).range
  let i : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin L' (A : Set E)).toSubsemiring := by
    rw [adjoin_intermediateField_toSubalgebra_of_isAlgebraic _ _ halg.symm,
      Algebra.adjoin_toSubsemiring, Algebra.adjoin_toSubsemiring]
    congr 2
    ext x
    simp only [Set.mem_range, Subtype.exists]
    exact ⟨fun ⟨y, h⟩ ↦ ⟨x, ⟨y, h⟩, rfl⟩, fun ⟨a, ⟨y, h1⟩, h2⟩ ↦ ⟨y, h1.trans h2⟩⟩
  refine rank_eq_of_equiv_equiv i (RingEquiv.subsemiringCongr heq).toAddEquiv
    i.bijective fun a ⟨x, hx⟩ ↦ ?_
  ext
  simp_rw [Algebra.smul_def]
  rfl
/-
**IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic_left*
* 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_left_of_isAlgebraic_left (H : A.LinearDisjoint L) [Alg
ebra.IsAlgebraic F A] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic
`：adjoin_rank_eq_rank_left_of_isAlgebraic (H : A.LinearDisjoint L) (halg : Algeb
ra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank L …
-/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A :=
  H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl ‹_›)
/-
**IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic_right
** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_left_of_isAlgebraic_right (H : A.LinearDisjoint L) [Al
gebra.IsAlgebraic F L] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic
`：adjoin_rank_eq_rank_left_of_isAlgebraic (H : A.LinearDisjoint L) (halg : Algeb
ra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank L …
-/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A :=
  H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inr ‹_›)

/-- If `A` and `L` are linearly disjoint over `F`, one of them is algebraic,
then `[L(A) : A] = [L : F]`. Note that in Lean `L(A)` is not naturally an `A`-algebra,
so this result is stated in a cumbersome way. -/
/-
**IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_isAlge
braic** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDisjoint L
) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Cardinal.lift.{w}
 (Module.rank A (extendScalars (show A <= (adjoin L (A : Set E)).restrictScalars
 F from subset_adjoin L (A : Set E)))) = Cardinal.lift.{v} (Module.rank F L)
参数：H : A.LinearDisjoint L；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F
 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right`：adjoin_rank_eq_rank
_right [Module.Free R B] [Module.Flat R A] [Nontrivial R] [Nontrivial S] : Modul
e.rank A (Algebra.adjoin A (B : Set S)) =…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic`：
adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
 (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) …
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Algebra.adjoin_toSubsemiring`：∀ (R : Type u) {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set A),   (Algebra.a
djoin R s).toSubse…
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `rank_eq_of_equiv_equiv`：rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M
₁) (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) : Mod
ule.rank R M…
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` and `L` are linearly disjoint over `F`, one of them is algebraic,
then `[L(A) : A] = [L : F]`. Note that in Lean `L(A)` is not naturally an `A`-al
gebra,
so this result is stated in a cumbersome way.
-/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) := by
  rw [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.lift_rank_eq,
    Cardinal.lift_inj, ← Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right H]
  set L' := (IsScalarTower.toAlgHom F L E).range
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin A (L' : Set E)).toSubsemiring := by
    rw [adjoin_intermediateField_toSubalgebra_of_isAlgebraic _ _ halg.symm,
      Algebra.adjoin_toSubsemiring, Algebra.adjoin_toSubsemiring, Set.union_comm]
    congr 2
    ext x
    simp
  refine rank_eq_of_equiv_equiv (RingHom.id A) (RingEquiv.subsemiringCongr heq).toAddEquiv
    Function.bijective_id fun ⟨a, ha⟩ ⟨x, hx⟩ ↦ ?_
  ext
  simp_rw [Algebra.smul_def]
  rfl
/-
**IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_isAlge
braic_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left (H : A.LinearDisjo
int L) [Algebra.IsAlgebraic F A] : Cardinal.lift.{w} (Module.rank A (extendScala
rs (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A :
 Set E)))) = Cardinal.lift.{v} (Module.rank F L)
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_
isAlgebraic`：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDis
joint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Car…
-/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) :=
  H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inl ‹_›)
/-
**IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_isAlge
braic_right** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right (H : A.LinearDisj
oint L) [Algebra.IsAlgebraic F L] : Cardinal.lift.{w} (Module.rank A (extendScal
ars (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A 
: Set E)))) = Cardinal.lift.{v} (Module.rank F L)
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_
isAlgebraic`：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDis
joint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Car…
-/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) :=
  H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inr ‹_›)

/-- If `A` is an intermediate field of `E / F`, `L` is an abstract field between `E / F`,
such that they are linearly disjoint over `F`, and one of them is algebraic, then
`[L : F] * [E : L(A)] = [E : A]`. -/
/-
**IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq_of_is
Algebraic** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoi
nt L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Cardinal.lift
.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E
) = Cardinal.lift.{w} (Module.rank A E)
参数：H : A.LinearDisjoint L；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F
 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_
isAlgebraic`：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDis
joint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Car…
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
If `A` is an intermediate field of `E / F`, `L` is an abstract field between `E 
/ F`,
such that they are linearly disjoint over `F`, and one of them is algebraic, the
n
`[L : F] * [E : L(A)] = [E : A]`.
-/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) := by
  rw [← H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg, ← Cardinal.lift_mul,
    Cardinal.lift_inj]
  exact rank_mul_rank A (extendScalars
    (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E))) E
/-
**IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq_of_is
Algebraic_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearD
isjoint L) [Algebra.IsAlgebraic F A] : Cardinal.lift.{v} (Module.rank F L) * Car
dinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) = Cardinal.lift.{w} (Modul
e.rank A E)
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq
_of_isAlgebraic`：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.L
inearDisjoint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :…
-/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) :=
  H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)
/-
**IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq_of_is
Algebraic_right** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right (H : A.Linear
Disjoint L) [Algebra.IsAlgebraic F L] : Cardinal.lift.{v} (Module.rank F L) * Ca
rdinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) = Cardinal.lift.{w} (Modu
le.rank A E)
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq
_of_isAlgebraic`：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.L
inearDisjoint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :…
-/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) :=
  H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

section

variable {L : Type v} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/-- The same-universe version of
`IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic`. -/
/-
**IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebraic** 是 
Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_right_of_isAlgebraic (H : A.LinearDisjoint L) (halg : 
Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank A (extendScalar
s (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : 
Set E))) = Module.rank F L
参数：H : A.LinearDisjoint L；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F
 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_
isAlgebraic`：lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDis
joint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Car…

--- 原说明 ---
The same-universe version of
`IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_isAlgeb
raic`.
-/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank A (extendScalars (show A ≤ (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L := by
  simpa only [Cardinal.lift_id] using H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg
/-
**IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebraic_left
** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L) [Al
gebra.IsAlgebraic F A] : Module.rank A (extendScalars (show A <= (adjoin L (A : 
Set E)).restrictScalars F from subset_adjoin L (A : Set E))) = Module.rank F L
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebrai
c`：adjoin_rank_eq_rank_right_of_isAlgebraic (H : A.LinearDisjoint L) (halg : Alg
ebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank A…
-/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Module.rank A (extendScalars (show A ≤ (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L :=
  H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inl ‹_›)
/-
**IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebraic_righ
t** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：adjoin_rank_eq_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L) [A
lgebra.IsAlgebraic F L] : Module.rank A (extendScalars (show A <= (adjoin L (A :
 Set E)).restrictScalars F from subset_adjoin L (A : Set E))) = Module.rank F L
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebrai
c`：adjoin_rank_eq_rank_right_of_isAlgebraic (H : A.LinearDisjoint L) (halg : Alg
ebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank A…
-/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Module.rank A (extendScalars (show A ≤ (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L :=
  H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inr ‹_›)

/-- The same-universe version of
`IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic`. -/
/-
**IntermediateField.LinearDisjoint.rank_right_mul_adjoin_rank_eq_of_isAlgebraic*
* 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：rank_right_mul_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L) (hal
g : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.rank F L * Modul
e.rank (adjoin L (A : Set E)) E = Module.rank A E
参数：H : A.LinearDisjoint L；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F
 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq
_of_isAlgebraic`：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.L
inearDisjoint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :…

--- 原说明 ---
The same-universe version of
`IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq_of_isA
lgebraic`.
-/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E := by
  simpa only [Cardinal.lift_id] using H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic halg
/-
**IntermediateField.LinearDisjoint.rank_right_mul_adjoin_rank_eq_of_isAlgebraic_
left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
 [Algebra.IsAlgebraic F A] : Module.rank F L * Module.rank (adjoin L (A : Set E)
) E = Module.rank A E
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.rank_right_mul_adjoin_rank_eq_of_isAlge
braic`：rank_right_mul_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L) (ha
lg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.ra…
-/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E :=
  H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)
/-
**IntermediateField.LinearDisjoint.rank_right_mul_adjoin_rank_eq_of_isAlgebraic_
right** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L
) [Algebra.IsAlgebraic F L] : Module.rank F L * Module.rank (adjoin L (A : Set E
)) E = Module.rank A E
参数：H : A.LinearDisjoint L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.rank_right_mul_adjoin_rank_eq_of_isAlge
braic`：rank_right_mul_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L) (ha
lg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : Module.ra…
-/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E :=
  H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

end

/-- If `A` and `L` have coprime degree over `F`, then they are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_finrank_coprime** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField.LinearDisjoint`。
形式化陈述：of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDis
joint L
参数：H : (finrank F A).Coprime (finrank F L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_finrank_coprime_of_free`：of_finrank_coprime
_of_free [Module.Free R A] [Module.Free R B] [Module.Free A (Algebra.adjoin A (B
 : Set S))] [Module.Free B (Algebra.adjoin…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用引理 `SubfieldClass.nnratCast_mem`：nnratCast_mem (s : S) (q : Rat>=0) : (q : K
) in s
· 使用引理 `SubfieldClass.ratCast_mem`：ratCast_mem (s : S) (q : Rat) : (q : K) in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `A` and `L` have coprime degree over `F`, then they are linearly disjoint.
-/
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDisjoint L :=
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
    inferInstanceAs <| Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
  letI : Field A.toSubalgebra := inferInstanceAs <| Field A
  Subalgebra.LinearDisjoint.of_finrank_coprime_of_free <| by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H

/-- If `A` and `L` are linearly disjoint over `F`, then `A ⊗[F] L` is a domain. -/
/-
**IntermediateField.LinearDisjoint.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField.LinearDisjoint`。
形式化陈述：isDomain (H : A.LinearDisjoint L) : IsDomain (A otimes[F] L)
参数：H : A.LinearDisjoint L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.isDomain`：isDomain [IsDomain S] : IsDomain (A 
otimes[R] B)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `A` and `L` are linearly disjoint over `F`, then `A ⊗[F] L` is a domain.
-/
theorem isDomain (H : A.LinearDisjoint L) : IsDomain (A ⊗[F] L) :=
  have : IsDomain (A ⊗[F] _) := Subalgebra.LinearDisjoint.isDomain H
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))).toMulEquiv.isDomain

/-- If `A` and `B` are field extensions of `F`, there exists a field extension `E` of `F` that
`A` and `B` embed into with linearly disjoint images, then `A ⊗[F] B` is a domain. -/
/-
**IntermediateField.LinearDisjoint.isDomain'** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField.LinearDisjoint`。
形式化陈述：isDomain' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B] {f
a : A ->ₐ[F] E} {fb : B ->ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRang
e) : IsDomain (A otimes[F] B)
参数：H : fa.fieldRange.LinearDisjoint fb.fieldRange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.isDomain_of_injective`：isDomain_of_injective [
IsDomain S] {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] 
{fa : A ->ₐ[R] S} {fb : B ->ₐ[R] S} (…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.fieldRange_toSubalgebra`：∀ {K : Type u_1} {L : Type u_2} {L' : Ty
pe u_3} [inst : Field K] [inst_1 : Field L] [inst_2 : Field L']   [inst_3 : Alge
bra K L] [inst_4 : A…

--- 原说明 ---
If `A` and `B` are field extensions of `F`, there exists a field extension `E` o
f `F` that
`A` and `B` embed into with linearly disjoint images, then `A ⊗[F] B` is a domai
n.
-/
theorem isDomain' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
    {fa : A →ₐ[F] E} {fb : B →ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRange) :
    IsDomain (A ⊗[F] B) := by
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra] at H
  exact H.isDomain_of_injective fa.injective fb.injective

/-- If `A ⊗[F] L` is a field, then `A` and `L` are linearly disjoint over `F`. -/
/-
**IntermediateField.LinearDisjoint.of_isField** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField.LinearDisjoint`。
形式化陈述：of_isField (H : IsField (A otimes[F] L)) : A.LinearDisjoint L
参数：H : IsField (A otimes[F] L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.of_isField`：of_isField (H : IsField (A otimes[
R] B)) : A.LinearDisjoint B
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `A ⊗[F] L` is a field, then `A` and `L` are linearly disjoint over `F`.
-/
theorem of_isField (H : IsField (A ⊗[F] L)) : A.LinearDisjoint L := by
  apply Subalgebra.LinearDisjoint.of_isField
  -- need these otherwise the `exact` will stuck at typeclass
  have : SMulCommClass F A A := SMulCommClass.of_commMonoid F A A
  have : SMulCommClass F A.toSubalgebra A.toSubalgebra := ‹SMulCommClass F A A›
  let : Mul (A ⊗[F] L) := Algebra.TensorProduct.instMul
  let : Mul (A.toSubalgebra ⊗[F] (IsScalarTower.toAlgHom F L E).range) :=
    Algebra.TensorProduct.instMul
  exact Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))
      |>.symm.toMulEquiv.isField H

/-- If `A` and `B` are field extensions of `F`, such that `A ⊗[F] B` is a field, then for any
field extension of `F` that `A` and `B` embed into, their images are linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.of_isField'** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField.LinearDisjoint`。
形式化陈述：of_isField' {A : Type v} [Field A] {B : Type w} [Field B] [Algebra F A] [A
lgebra F B] (H : IsField (A otimes[F] B)) {K : Type*} [Field K] [Algebra F K] (f
a : A ->ₐ[F] K) (fb : B ->ₐ[F] K) : fa.fieldRange.LinearDisjoint fb.fieldRange
参数：H : IsField (A otimes[F] B)；fa : A ->ₐ[F] K；fb : B ->ₐ[F] K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `Subalgebra.LinearDisjoint.of_isField`：of_isField (H : IsField (A otimes[
R] B)) : A.LinearDisjoint B
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `A` and `B` are field extensions of `F`, such that `A ⊗[F] B` is a field, the
n for any
field extension of `F` that `A` and `B` embed into, their images are linearly di
sjoint.
-/
theorem of_isField' {A : Type v} [Field A] {B : Type w} [Field B]
    [Algebra F A] [Algebra F B] (H : IsField (A ⊗[F] B))
    {K : Type*} [Field K] [Algebra F K] (fa : A →ₐ[F] K) (fb : B →ₐ[F] K) :
    fa.fieldRange.LinearDisjoint fb.fieldRange := by
  rw [linearDisjoint_iff']
  apply Subalgebra.LinearDisjoint.of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa fa.injective)
    (AlgEquiv.ofInjective fb fb.injective) |>.symm.toMulEquiv.isField H

variable (F) in
/-- If `A` and `B` are field extensions of `F`, such that `A ⊗[F] B` is a domain, then there exists
a field extension of `F` that `A` and `B` embed into with linearly disjoint images. -/
/-
**IntermediateField.LinearDisjoint.exists_field_of_isDomain** 是 Mathlib 中的一个定理，位
于命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：exists_field_of_isDomain (A : Type v) [Field A] (B : Type w) [Field B] [Al
gebra F A] [Algebra F B] [IsDomain (A otimes[F] B)] : exists (K : Type (max v w)
) (_ : Field K) (_ : Algebra F K) (fa : A ->ₐ[F] K) (fb : B ->ₐ[F] K), fa.fieldR
ange.LinearDisjoint fb.fieldRange
参数：A : Type v；B : Type w；A otimes[F] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`：exists_
field_of_isDomain_of_injective (A : Type v) [CommRing A] (B : Type w) [CommRing 
B] [Algebra R A] [Algebra R B] [Module.Flat R A] [Mod…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra

--- 原说明 ---
If `A` and `B` are field extensions of `F`, such that `A ⊗[F] B` is a domain, th
en there exists
a field extension of `F` that `A` and `B` embed into with linearly disjoint imag
es.
-/
theorem exists_field_of_isDomain (A : Type v) [Field A] (B : Type w) [Field B]
    [Algebra F A] [Algebra F B] [IsDomain (A ⊗[F] B)] :
    ∃ (K : Type (max v w)) (_ : Field K) (_ : Algebra F K) (fa : A →ₐ[F] K) (fb : B →ₐ[F] K),
    fa.fieldRange.LinearDisjoint fb.fieldRange :=
  have ⟨K, inst1, inst2, fa, fb, _, _, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F A B
      (RingHom.injective _) (RingHom.injective _)
  ⟨K, inst1, inst2, fa, fb, linearDisjoint_iff'.2 H⟩

variable (F) in
/-- If for any field extension `K` of `F` that `A` and `B` embed into, their images are
linearly disjoint, then `A ⊗[F] B` is a field. (In the proof we choose `K` to be the quotient
of `A ⊗[F] B` by a maximal ideal.) -/
/-
**IntermediateField.LinearDisjoint.isField_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField.LinearDisjoint`。
形式化陈述：isField_of_forall (A : Type v) [Field A] (B : Type w) [Field B] [Algebra F
 A] [Algebra F B] (H : forall (K : Type (max v w)) [Field K] [Algebra F K], fora
ll (fa : A ->ₐ[F] K) (fb : B ->ₐ[F] K), fa.fieldRange.LinearDisjoint fb.fieldRan
ge) : IsField (A otimes[F] B)
参数：A : Type v；B : Type w；H : forall (K : Type (max v w)) [Field K] [Algebra F K]
, forall (fa : A ->ₐ[F] K) (fb : B ->ₐ[F] K), fa.fieldRange.LinearDisjoint fb.fi
eldRange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_maximal`：exists_maximal [Nontrivial α] : exists M : Ideal α
, M.IsMaximal
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If for any field extension `K` of `F` that `A` and `B` embed into, their images 
are
linearly disjoint, then `A ⊗[F] B` is a field. (In the proof we choose `K` to be
 the quotient
of `A ⊗[F] B` by a maximal ideal.)
-/
theorem isField_of_forall (A : Type v) [Field A] (B : Type w) [Field B]
    [Algebra F A] [Algebra F B]
    (H : ∀ (K : Type (max v w)) [Field K] [Algebra F K],
      ∀ (fa : A →ₐ[F] K) (fb : B →ₐ[F] K), fa.fieldRange.LinearDisjoint fb.fieldRange) :
    IsField (A ⊗[F] B) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A ⊗[F] B)
  apply not_imp_not.1 (Ring.ne_bot_of_isMaximal_of_not_isField hM)
  let K : Type (max v w) := A ⊗[F] B ⧸ M
  let : Field K := Ideal.Quotient.field _
  let i := IsScalarTower.toAlgHom F (A ⊗[F] B) K
  let fa := i.comp (Algebra.TensorProduct.includeLeft : A →ₐ[F] _)
  let fb := i.comp (Algebra.TensorProduct.includeRight : B →ₐ[F] _)
  replace H := H K fa fb
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra,
    Subalgebra.linearDisjoint_iff_injective] at H
  have hi : i = (fa.range.mulMap fb.range).comp (Algebra.TensorProduct.congr
      (AlgEquiv.ofInjective fa fa.injective) (AlgEquiv.ofInjective fb fb.injective)) := by
    ext <;> simp [fa, fb]
  replace H : Function.Injective i := by simpa only
    [hi, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, EquivLike.injective_comp, fa, this, K, fb]
  change Function.Injective (Ideal.Quotient.mk M) at H
  rwa [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker] at H

variable (F E) in
/-- If `E` and `K` are field extensions of `F`, one of them is algebraic, such that
`E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field. It is a corollary of
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` and
`IntermediateField.sup_toSubalgebra_of_isAlgebraic`.
See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earlier file). -/
/-
**IntermediateField.LinearDisjoint._root_.Algebra.TensorProduct.isField_of_isAlg
ebraic** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.LinearDisjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` and `K` are field extensions of `F`, one of them is algebraic, such that
`E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field. It is a corollary of
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` and
`IntermediateField.sup_toSubalgebra_of_isAlgebraic`.
See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earli
er file).
-/
theorem _root_.Algebra.TensorProduct.isField_of_isAlgebraic
    (K : Type*) [Field K] [Algebra F K] [IsDomain (E ⊗[F] K)]
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K) : IsField (E ⊗[F] K) :=
  have ⟨L, _, _, fa, fb, hfa, hfb, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F E K
      (RingHom.injective _) (RingHom.injective _)
  let f : E ⊗[F] K ≃ₐ[F] ↥(fa.fieldRange ⊔ fb.fieldRange) :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)
    |>.trans (Subalgebra.LinearDisjoint.mulMap H)
    |>.trans (Subalgebra.equivOfEq _ _
      (sup_toSubalgebra_of_isAlgebraic fa.fieldRange fb.fieldRange <| by
        rwa [(AlgEquiv.ofInjective fa hfa).isAlgebraic_iff,
          (AlgEquiv.ofInjective fb hfb).isAlgebraic_iff] at halg).symm)
  f.toMulEquiv.isField (Field.toIsField _)

/-- If `A` and `L` are linearly disjoint over `F` and one of them is algebraic,
then `A ⊗[F] L` is a field. -/
/-
**IntermediateField.LinearDisjoint.isField_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：isField_of_isAlgebraic (H : A.LinearDisjoint L) (halg : Algebra.IsAlgebrai
c F A ∨ Algebra.IsAlgebraic F L) : IsField (A otimes[F] L)
参数：H : A.LinearDisjoint L；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F
 L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.isDomain`：isDomain (H : A.LinearDisjoin
t L) : IsDomain (A otimes[F] L)
· 使用定理 `Algebra.TensorProduct.isField_of_isAlgebraic`：∀ (F : Type u) (E : Type v
) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K : Type u_1) [ins
t_3 : Field K]   [inst_4 : Algebra…

--- 原说明 ---
If `A` and `L` are linearly disjoint over `F` and one of them is algebraic,
then `A ⊗[F] L` is a field.
-/
theorem isField_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : IsField (A ⊗[F] L) :=
  have := H.isDomain
  Algebra.TensorProduct.isField_of_isAlgebraic F A L halg

/-- If `A` and `B` are field extensions of `F`, one of them is algebraic, such that there exists a
field `E` that `A` and `B` embeds into with linearly disjoint images, then `A ⊗[F] B`
is a field. -/
/-
**IntermediateField.LinearDisjoint.isField_of_isAlgebraic'** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：isField_of_isAlgebraic' {A B : Type*} [Field A] [Algebra F A] [Field B] [A
lgebra F B] {fa : A ->ₐ[F] E} {fb : B ->ₐ[F] E} (H : fa.fieldRange.LinearDisjoin
t fb.fieldRange) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) : Is
Field (A otimes[F] B)
参数：H : fa.fieldRange.LinearDisjoint fb.fieldRange；halg : Algebra.IsAlgebraic F A
 ∨ Algebra.IsAlgebraic F B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.isDomain'`：isDomain' {A B : Type*} [Fie
ld A] [Algebra F A] [Field B] [Algebra F B] {fa : A ->ₐ[F] E} {fb : B ->ₐ[F] E} 
(H : fa.fieldRange.LinearDisjoin…
· 使用定理 `Algebra.TensorProduct.isField_of_isAlgebraic`：∀ (F : Type u) (E : Type v
) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K : Type u_1) [ins
t_3 : Field K]   [inst_4 : Algebra…

--- 原说明 ---
If `A` and `B` are field extensions of `F`, one of them is algebraic, such that 
there exists a
field `E` that `A` and `B` embeds into with linearly disjoint images, then `A ⊗[
F] B`
is a field.
-/
theorem isField_of_isAlgebraic' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
    {fa : A →ₐ[F] E} {fb : B →ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRange)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) : IsField (A ⊗[F] B) :=
  have := H.isDomain'
  Algebra.TensorProduct.isField_of_isAlgebraic F A B halg

/-- If `A` and `L` are linearly disjoint, one of them is algebraic, then for any `B` and `L'`
isomorphic to `A` and `L` respectively, `B` and `L'` are also linearly disjoint. -/
/-
**IntermediateField.LinearDisjoint.algEquiv_of_isAlgebraic** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField.LinearDisjoint`。
形式化陈述：algEquiv_of_isAlgebraic (H : A.LinearDisjoint L) {E' : Type*} [Field E'] [
Algebra F E'] (B : IntermediateField F E') (L' : Type*) [Field L'] [Algebra F L'
] [Algebra L' E'] [IsScalarTower F L' E'] (f1 : A ≃ₐ[F] B) (f2 : L ≃ₐ[F] L') (ha
lg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : B.LinearDisjoint L'
参数：H : A.LinearDisjoint L；B : IntermediateField F E'；L' : Type*；f1 : A ≃ₐ[F] B；f
2 : L ≃ₐ[F] L'；halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.of_isField`：of_isField (H : IsField (A 
otimes[F] L)) : A.LinearDisjoint L
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `IntermediateField.LinearDisjoint.isField_of_isAlgebraic`：isField_of_isAl
gebraic (H : A.LinearDisjoint L) (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlg
ebraic F L) : IsField (A otimes[F] L)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
If `A` and `L` are linearly disjoint, one of them is algebraic, then for any `B`
 and `L'`
isomorphic to `A` and `L` respectively, `B` and `L'` are also linearly disjoint.
-/
theorem algEquiv_of_isAlgebraic (H : A.LinearDisjoint L)
    {E' : Type*} [Field E'] [Algebra F E']
    (B : IntermediateField F E')
    (L' : Type*) [Field L'] [Algebra F L'] [Algebra L' E'] [IsScalarTower F L' E']
    (f1 : A ≃ₐ[F] B) (f2 : L ≃ₐ[F] L')
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    B.LinearDisjoint L' :=
  .of_isField ((Algebra.TensorProduct.congr f1 f2).symm.toMulEquiv.isField
    (H.isField_of_isAlgebraic halg))

/--
If `A` and `B` are linearly disjoint, then `trace` and `algebraMap` commutes.
-/
/-
**IntermediateField.LinearDisjoint.trace_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField.LinearDisjoint`。
形式化陈述：trace_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A
 ⊔ B = ⊤) (x : B) : Algebra.trace A E (algebraMap B E x) = algebraMap F A (Algeb
ra.trace F B x)
参数：h₁ : A.LinearDisjoint B；h₂ : A ⊔ B = ⊤；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.trace_algebraMap`：trace_algebraMap (H : A.Line
arDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B] [Module.Finite R B] (x : B) : A
lgebra.trace A S (algebraMap B S…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`：sup_toSubalgebr
a_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E2).toSubalgebra = E1.
toSubalgebra ⊔ E2.toSubalgebra
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
If `A` and `B` are linearly disjoint, then `trace` and `algebraMap` commutes.
-/
theorem trace_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
    (x : B) :
    Algebra.trace A E (algebraMap B E x) = algebraMap F A (Algebra.trace F B x) := by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.trace_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

/--
If `A` and `B` are linearly disjoint, then `norm` and `algebraMap` commutes.
-/
/-
**IntermediateField.LinearDisjoint.norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField.LinearDisjoint`。
形式化陈述：norm_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A 
⊔ B = ⊤) (x : B) : Algebra.norm A (algebraMap B E x) = algebraMap F A (Algebra.n
orm F x)
参数：h₁ : A.LinearDisjoint B；h₂ : A ⊔ B = ⊤；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.LinearDisjoint.norm_algebraMap`：norm_algebraMap (H : A.Linear
Disjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B] [Module.Finite R B] (x : B) : Alg
ebra.norm A (algebraMap B S x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.linearDisjoint_iff'`：linearDisjoint_iff' : A.LinearDis
joint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`：sup_toSubalgebr
a_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E2).toSubalgebra = E1.
toSubalgebra ⊔ E2.toSubalgebra
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
If `A` and `B` are linearly disjoint, then `norm` and `algebraMap` commutes.
-/
theorem norm_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
    (x : B) :
    Algebra.norm A (algebraMap B E x) = algebraMap F A (Algebra.norm F x) := by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.norm_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

end LinearDisjoint

end IntermediateField

