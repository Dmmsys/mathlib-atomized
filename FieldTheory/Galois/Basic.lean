/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz, Yongle Hu, Jingting Wang
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `IsGalois F E` where `E` is an extension of `F`
- `fixedField H` where `H : Subgroup Gal(E/F)`
- `fixingSubgroup K` where `K : IntermediateField F E`
- `intermediateFieldEquivSubgroup` where `E/F` is finite dimensional and Galois

## Main results

- `IntermediateField.fixingSubgroup_fixedField` : If `E/F` is finite dimensional (but not
  necessarily Galois) then `fixingSubgroup (fixedField H) = H`
- `IsGalois.fixedField_fixingSubgroup`: If `E/F` is finite dimensional and Galois
  then `fixedField (fixingSubgroup K) = K`

Together, these two results prove the Galois correspondence.

- `IsGalois.tfae` : Equivalent characterizations of a Galois extension of finite degree

## Additional results

- Instances for `Algebra.IsQuadraticExtension`: a quadratic extension is Galois (if separable)
  with cyclic and thus abelian Galois group.

-/

@[expose] public section


open scoped Polynomial IntermediateField

open Module AlgEquiv IntermediateField

section

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

/-- A field extension E/F is Galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
@[stacks 09I0]
/-
**IsGalois** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → [inst : Field F] → (E : Type u_2) → [inst_1 : Field E] → 
[Algebra F E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field extension E/F is Galois if it is both separable and normal. Note that in
 mathlib
a separable extension of fields is by definition algebraic.
-/
class IsGalois : Prop where
  [to_isSeparable : Algebra.IsSeparable F E]
  [to_normal : Normal F E]

variable {F E}
/-
**isGalois_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGalois_iff : IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isGalois_iff : IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_isSeparable := h.1
      to_normal := h.2 }⟩

attribute [instance 100] IsGalois.to_isSeparable IsGalois.to_normal

-- see Note [lower instance priority]
variable (F E)

namespace IsGalois

/-
**IsGalois.self** 是 Mathlib 中的一个实例，位于命名空间 `IsGalois`。
形式化陈述：self : IsGalois F F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance self : IsGalois F F :=
  ⟨⟩

variable {E}
/-
**IsGalois.integral** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：integral [IsGalois F E] (x : E) : IsIntegral F x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.isIntegral`：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegr
al F x
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
-/
theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  to_normal.isIntegral x
/-
**IsGalois.separable** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：separable [IsGalois F E] (x : E) : IsSeparable F x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
-/
theorem separable [IsGalois F E] (x : E) : IsSeparable F x :=
  Algebra.IsSeparable.isSeparable F x
/-
**IsGalois.splits** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：splits [IsGalois F E] (x : E) : ((minpoly F x).map (algebraMap F E)).Split
s
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.splits'`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {inst_1
 : Field K} {inst_2 : Algebra F K} [self : Normal F K] (x : K),   (Polynomial.ma
p (a…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
-/
theorem splits [IsGalois F E] (x : E) : ((minpoly F x).map (algebraMap F E)).Splits :=
  Normal.splits' x

variable (E)

/-- Let $E$ be a field. Let $G$ be a finite group acting on $E$.
Then the extension $E / E^G$ is Galois. -/
@[stacks 09I3 "first part"]
/-
**IsGalois.of_fixed_field** 是 Mathlib 中的一个实例，位于命名空间 `IsGalois`。
形式化陈述：of_fixed_field (G : Type*) [Group G] [Finite G] [MulSemiringAction G E] : 
IsGalois (FixedPoints.subfield G E) E
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let $E$ be a field. Let $G$ be a finite group acting on $E$.
Then the extension $E / E^G$ is Galois.
-/
instance of_fixed_field (G : Type*) [Group G] [Finite G] [MulSemiringAction G E] :
    IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩
/-
**IsGalois.IntermediateField.AdjoinSimple.card_aut_eq_finrank** 是 Mathlib 中的一个定理
，位于命名空间 `IsGalois.IntermediateField.AdjoinSimple`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] (E : Type u_2) [inst_1 : Field E] [inst_
2 : Algebra F E] [FiniteDimensional F E]   {α : E},   IsIntegral F α →     IsSep
arable F α →       (Polynomial.map (algebraMap F ↥F⟮α⟯) (minpoly F α)).Splits → 
Nat.card Gal(↥F⟮α⟯/F) = Module.finrank F ↥F⟮α⟯
参数：F : Type u_1；E : Type u_2；Polynomial.map (algebraMap F ↥F⟮α⟯) (minpoly F α)；↥
F⟮α⟯/F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.card_algHom_adjoin_integral`：card_algHom_adjoin_integr
al (h : IsIntegral F α) (h_sep : IsSeparable F α) (h_splits : ((minpoly F α).map
 (algebraMap F K)).Splits) : Nat.ca…
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem IntermediateField.AdjoinSimple.card_aut_eq_finrank [FiniteDimensional F E] {α : E}
    (hα : IsIntegral F α) (h_sep : IsSeparable F α)
    (h_splits : ((minpoly F α).map (algebraMap F F⟮α⟯)).Splits) :
    Nat.card Gal(F⟮α⟯/F) = finrank F F⟮α⟯ := by
  rw [IntermediateField.adjoin.finrank hα]
  rw [← IntermediateField.card_algHom_adjoin_integral F hα h_sep h_splits]
  exact Nat.card_congr (algEquivEquivAlgHom F F⟮α⟯)

/-- Let $E / F$ be a finite extension of fields. If $E$ is Galois over $F$, then
$|\text{Aut}(E/F)| = [E : F]$. -/
@[stacks 09I1 "'only if' part"]
/-
**IsGalois.card_aut_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] : Nat.card Gal(
E/F) = finrank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.exists_primitive_element`：exists_primitive_element : exists α : E,
 F⟮α⟯ = ⊤
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `IsGalois.integral`：integral [IsGalois F E] (x : E) : IsIntegral F x
· 使用定理 `IsGalois.separable`：separable [IsGalois F E] (x : E) : IsSeparable F x
· 使用定理 `IsGalois.splits`：splits [IsGalois F E] (x : E) : ((minpoly F x).map (alg
ebraMap F E)).Splits
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `IsGalois.IntermediateField.AdjoinSimple.card_aut_eq_finrank`：∀ (F : Type
 u_1) [inst : Field F] (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra F E] 
[FiniteDimensional F E]   {α : E},   IsIntegral F…
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β

--- 原说明 ---
Let $E / F$ be a finite extension of fields. If $E$ is Galois over $F$, then
$|\text{Aut}(E/F)| = [E : F]$.
-/
theorem card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Nat.card Gal(E/F) = finrank F E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let iso : F⟮α⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e => ⟨e, by rw [hα]; exact IntermediateField.mem_top⟩
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H : IsIntegral F α := IsGalois.integral F α
  have h_sep : IsSeparable F α := IsGalois.separable F α
  have h_splits : ((minpoly F α).map (algebraMap F E)).Splits := IsGalois.splits F α
  replace h_splits : ((minpoly F α).map (algebraMap F F⟮α⟯)).Splits := by
    simpa [Polynomial.map_map] using! h_splits.map iso.symm.toRingHom
  rw [← LinearEquiv.finrank_eq iso.toLinearEquiv]
  rw [← IntermediateField.AdjoinSimple.card_aut_eq_finrank F E H h_sep h_splits]
  apply Nat.card_congr
  exact Equiv.mk (fun ϕ => iso.trans (ϕ.trans iso.symm)) fun ϕ => iso.symm.trans (ϕ.trans iso)

/-- A galois extension with finite galois group is finite dimensional.
The dimension is then equal to the order of the galois group via `IsGalois.card_aut_eq_finrank`. -/
/-
**IsGalois.finiteDimensional_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsGalois`。
形式化陈述：finiteDimensional_of_finite [IsGalois F E] [Finite Gal(E/F)] : FiniteDimen
sional F E
参数：E/F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IntermediateField.exists_lt_finrank_of_infinite_dimensional`：exists_lt_f
inrank_of_infinite_dimensional [Algebra.IsAlgebraic F E] (hnfd : ¬ FiniteDimensi
onal F E) (n : Nat) : exists L : IntermediateFiel…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `IntermediateField.finrank_le_of_le_right`：finrank_le_of_le_right [Finite
Dimensional K E] (h : F <= E) : finrank K F <= finrank K E
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L

--- 原说明 ---
A galois extension with finite galois group is finite dimensional.
The dimension is then equal to the order of the galois group via `IsGalois.card_
aut_eq_finrank`.
-/
lemma finiteDimensional_of_finite [IsGalois F E] [Finite Gal(E/F)] : FiniteDimensional F E := by
  by_contra H
  obtain ⟨K, h₁, h₂⟩ := exists_lt_finrank_of_infinite_dimensional H (Nat.card Gal(E/F))
  let K' := normalClosure F K E
  have : IsGalois F K' := ⟨⟩
  have := Nat.card_le_card_of_surjective _
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K') (E := E))
  rw [IsGalois.card_aut_eq_finrank] at this
  exact (this.trans_lt h₂).not_ge (finrank_le_of_le_right K.le_normalClosure)

end IsGalois

end

section IsGaloisTower

variable (F K E : Type*) [Field F] [Field K] [Field E] {E' : Type*} [Field E'] [Algebra F E']
variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

/-- Let $E / K / F$ be a tower of field extensions.
If $E$ is Galois over $F$, then $E$ is Galois over $K$. -/
@[stacks 09I2]
/-
**IsGalois.tower_top_of_isGalois** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGalois.tower_top_of_isGalois [IsGalois F E] : IsGalois K E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isSeparable_tower_top_of_isSeparable`：Algebra.isSeparable_tower_
top_of_isSeparable [Algebra.IsSeparable F E] : Algebra.IsSeparable L E
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Normal.tower_top_of_normal`：Normal.tower_top_of_normal [h : Normal F E] 
: Normal K E
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E

--- 原说明 ---
Let $E / K / F$ be a tower of field extensions.
If $E$ is Galois over $F$, then $E$ is Galois over $K$.
-/
theorem IsGalois.tower_top_of_isGalois [IsGalois F E] : IsGalois K E :=
  { to_isSeparable := Algebra.isSeparable_tower_top_of_isSeparable F K E
    to_normal := Normal.tower_top_of_normal F K E }

variable {F E}

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsGalois.tower_top_intermediateField (K : IntermediateField F E)
    [IsGalois F E] : IsGalois K E :=
  IsGalois.tower_top_of_isGalois F K E
/-
**isGalois_iff_isGalois_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGalois_iff_isGalois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGal
ois F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.tower_top_of_isGalois`：IsGalois.tower_top_of_isGalois [IsGalois
 F E] : IsGalois K E
· 使用定理 `IsGalois.tower_top_intermediateField`：∀ {F : Type u_1} {E : Type u_3} [i
nst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K : IntermediateField 
F E)   [IsGalois F E], IsG…
-/
theorem isGalois_iff_isGalois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E := by
  constructor
  · intro h
    exact IsGalois.tower_top_of_isGalois (⊥ : IntermediateField F E) F E
  · intro h; infer_instance
/-
**IsGalois.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E'
参数：f : E ≃ₐ[F] E'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.of_algHom`：Algebra.IsSeparable.of_algHom [Algebra.Is
Separable F E'] : Algebra.IsSeparable F E
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Normal.of_algEquiv`：Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E')
 : Normal F E'
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
-/
theorem IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_isSeparable := Algebra.IsSeparable.of_algHom F E f.symm
    to_normal := Normal.of_algEquiv f }
/-
**AlgEquiv.transfer_galois** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E'
参数：f : E ≃ₐ[F] E'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.of_algEquiv`：IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E
') : IsGalois F E'
-/
theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun _ => IsGalois.of_algEquiv f, fun _ => IsGalois.of_algEquiv f.symm⟩
/-
**isGalois_iff_isGalois_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGalois_iff_isGalois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGal
ois F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.transfer_galois`：AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : Is
Galois F E ↔ IsGalois F E'
-/
theorem isGalois_iff_isGalois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois
/-
**isGalois_bot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isGalois_bot : IsGalois F (⊥ : IntermediateField F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgEquiv.transfer_galois`：AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : Is
Galois F E ↔ IsGalois F E'
-/
instance isGalois_bot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)
/-
**IsGalois.of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGalois.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N] [h
 : IsGalois F E] {f : F ≃+* M} {g : E ≃+* N} (hcomp : (algebraMap M N).comp f = 
(g : E ->+* N).comp (algebraMap F E)) : IsGalois M N
参数：hcomp : (algebraMap M N).comp f = (g : E ->+* N).comp (algebraMap F E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isGalois_iff`：isGalois_iff : IsGalois F E ↔ Algebra.IsSeparable F E ∧ No
rmal F E
· 使用引理 `Algebra.IsSeparable.of_equiv_equiv`：Algebra.IsSeparable.of_equiv_equiv [
Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Normal.of_equiv_equiv`：Normal.of_equiv_equiv {M N : Type*} [Field N] [Fi
eld M] [Algebra M N] [h : Normal F E] {f : F ≃+* M} {g : E ≃+* N} (hcomp : (alge
braMap M N)…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
-/
theorem IsGalois.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N]
    [h : IsGalois F E] {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = (g : E →+* N).comp (algebraMap F E)) :
    IsGalois M N :=
  isGalois_iff.mpr ⟨Algebra.IsSeparable.of_equiv_equiv f g hcomp, Normal.of_equiv_equiv hcomp⟩

end IsGaloisTower

section GaloisCorrespondence

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (H : Subgroup Gal(E/F)) (K : IntermediateField F E)

/-- The intermediate field of fixed points fixed by a monoid action that commutes with the
`F`-action on `E`. -/
/-
**FixedPoints.intermediateField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.intermediateField (M : Type*) [Monoid M] [MulSemiringAction M 
E] [SMulCommClass M F E] : IntermediateField F E
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intermediate field of fixed points fixed by a monoid action that commutes wi
th the
`F`-action on `E`.
-/
def FixedPoints.intermediateField (M : Type*) [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] : IntermediateField F E :=
  { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebraMap_mem' := fun a g => smul_algebraMap g a }
/-
**FixedPoints.mem_intermediateField_iff** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] {M : Type u_3}   [inst_3 : Monoid M] [inst_4 : MulSemiringActio
n M E] [inst_5 : SMulCommClass M F E] {x : E},   x ∈ FixedPoints.intermediateFie
ld M ↔ ∀ (m : M), m • x = x
参数：m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma FixedPoints.mem_intermediateField_iff
    {M : Type*} [Monoid M] [MulSemiringAction M E] [SMulCommClass M F E] {x : E} :
    x ∈ FixedPoints.intermediateField (F := F) M ↔ ∀ m : M, m • x = x := .rfl

namespace IntermediateField

/-- The intermediate field fixed by a subgroup. -/
/-
**IntermediateField.fixedField** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：fixedField : IntermediateField F E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intermediate field fixed by a subgroup.
-/
def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H
/-
**IntermediateField.mem_fixedField_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (H : Subgroup Gal(E/F))   (x : E), x ∈ IntermediateField.fixedF
ield H ↔ ∀ f ∈ H, f x = x
参数：H : Subgroup Gal(E/F)；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_fixedField_iff (x) :
    x ∈ fixedField H ↔ ∀ f ∈ H, f x = x := by
  change x ∈ MulAction.fixedPoints H E ↔ _
  simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, AlgEquiv.smul_def]
/-
**IntermediateField.fixedField_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E],   IntermediateField.fixedField ⊥ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma fixedField_bot : fixedField (⊥ : Subgroup Gal(E/F)) = ⊤ := by
  ext
  simp
/-
**IntermediateField.finrank_fixedField_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：finrank_fixedField_eq_card [FiniteDimensional F E] : finrank (fixedField H
) E = Nat.card H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `FixedPoints.finrank_eq_card`：finrank_eq_card [Fintype G] [FaithfulSMul G
 F] : finrank (FixedPoints.subfield G F) F = Fintype.card G
· 使用定理 `Subgroup.instFaithfulSMulSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} [in
st : Group G] [inst_1 : MulAction G α] [FaithfulSMul G α] (S : Subgroup G),   Fa
ithfulSMul (↥S) α
-/
theorem finrank_fixedField_eq_card [FiniteDimensional F E] :
    finrank (fixedField H) E = Nat.card H := by
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E

/-- The subgroup fixing an intermediate field. -/
nonrec def fixingSubgroup : Subgroup Gal(E/F) :=
  fixingSubgroup Gal(E/F) (K : Set E)

/-
**IntermediateField.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：le_iff_le : K <= fixedField H ↔ H <= fixingSubgroup K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
-/
theorem le_iff_le : K ≤ fixedField H ↔ H ≤ fixingSubgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

/-- The map `K ↦ Gal(E/K)` is inclusion-reversing. -/
/-
**IntermediateField.fixingSubgroup_le** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：fixingSubgroup_le {K1 K2 : IntermediateField F E} (h12 : K1 <= K2) : K2.fi
xingSubgroup <= K1.fixingSubgroup
参数：h12 : K1 <= K2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `K ↦ Gal(E/K)` is inclusion-reversing.
-/
theorem fixingSubgroup_le {K1 K2 : IntermediateField F E} (h12 : K1 ≤ K2) :
    K2.fixingSubgroup ≤ K1.fixingSubgroup :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h12 hx⟩
/-
**IntermediateField.fixedField_le** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：fixedField_le {H1 H2 : Subgroup Gal(E/F)} (h12 : H1 <= H2) : fixedField H2
 <= fixedField H1
参数：E/F；h12 : H1 <= H2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixedField_le {H1 H2 : Subgroup Gal(E/F)} (h12 : H1 ≤ H2) :
    fixedField H2 ≤ fixedField H1 :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h12 hx⟩
/-
**IntermediateField.fixingSubgroup_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Intermedi
ateField`。
形式化陈述：fixingSubgroup_antitone : Antitone (@fixingSubgroup F _ E _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.fixingSubgroup_le`：fixingSubgroup_le {K1 K2 : Intermed
iateField F E} (h12 : K1 <= K2) : K2.fixingSubgroup <= K1.fixingSubgroup
-/
lemma fixingSubgroup_antitone : Antitone (@fixingSubgroup F _ E _ _) :=
  fun _ _ ↦ fixingSubgroup_le
/-
**IntermediateField.fixedField_antitone** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateF
ield`。
形式化陈述：fixedField_antitone : Antitone (@fixedField F _ E _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.fixedField_le`：fixedField_le {H1 H2 : Subgroup Gal(E/F
)} (h12 : H1 <= H2) : fixedField H2 <= fixedField H1
-/
lemma fixedField_antitone : Antitone (@fixedField F _ E _ _) :=
  fun _ _ ↦ fixedField_le
/-
**IntermediateField.mem_fixingSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (K : IntermediateField F E)   (σ : Gal(E/F)), σ ∈ K.fixingSubgr
oup ↔ ∀ x ∈ K, σ x = x
参数：K : IntermediateField F E；σ : Gal(E/F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
-/
@[simp] lemma mem_fixingSubgroup_iff (σ) : σ ∈ fixingSubgroup K ↔ ∀ x ∈ K, σ x = x :=
  _root_.mem_fixingSubgroup_iff _
/-
**IntermediateField.fixingSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E], ⊤.fixingSubgroup = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma fixingSubgroup_top : fixingSubgroup (⊤ : IntermediateField F E) = ⊥ := by
  ext
  simp [DFunLike.ext_iff]
/-
**IntermediateField.fixingSubgroup_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E], ⊥.fixingSubgroup = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma fixingSubgroup_bot : fixingSubgroup (⊥ : IntermediateField F E) = ⊤ := by
  ext
  simp [mem_bot]
/-
**IntermediateField.fixingSubgroup_sup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：fixingSubgroup_sup {K L : IntermediateField F E} : (K ⊔ L).fixingSubgroup 
= K.fixingSubgroup ⊓ L.fixingSubgroup
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用引理 `IntermediateField.fixingSubgroup_antitone`：fixingSubgroup_antitone : Ant
itone (@fixingSubgroup F _ E _ _)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fixingSubgroup_sup {K L : IntermediateField F E} :
    (K ⊔ L).fixingSubgroup = K.fixingSubgroup ⊓ L.fixingSubgroup := by
  ext φ
  exact ⟨fun h ↦ ⟨fixingSubgroup_antitone le_sup_left h, fixingSubgroup_antitone le_sup_right h⟩,
    by simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]⟩

/-- The fixing subgroup of `K : IntermediateField F E` is isomorphic to `Gal(E/K)`. -/
/-
**IntermediateField.fixingSubgroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateF
ield`。
形式化陈述：fixingSubgroupEquiv : fixingSubgroup K ≃* Gal(E/K) where toFun ϕ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fixing subgroup of `K : IntermediateField F E` is isomorphic to `Gal(E/K)`.
-/
def fixingSubgroupEquiv : fixingSubgroup K ≃* Gal(E/K) where
  toFun ϕ := { AlgEquiv.toRingEquiv (ϕ : Gal(E/F)) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  map_mul' _ _ := by ext; rfl
/-
**IntermediateField.fixingSubgroup_fixedField** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：fixingSubgroup_fixedField [FiniteDimensional F E] : fixingSubgroup (fixedF
ield H) = H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.le_iff_le`：le_iff_le : K <= fixedField H ↔ H <= fixing
Subgroup K
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `Subgroup.instFaithfulSMulSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} [in
st : Group G] [inst_1 : MulAction G α] [FaithfulSMul G α] (S : Subgroup G),   Fa
ithfulSMul (↥S) α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_inclusion_surjective`：eq_of_inclusion_surjective {s t : Set α}
 {h : s subseteq t} (h_surj : Function.Surjective (inclusion h)) : s = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.bijective_iff_injective_and_card`：∀ {α : Type u_1} {β : Type u_2} [F
inite β] (f : α → β),   Function.Bijective f ↔ Function.Injective f ∧ Nat.card α
 = Nat.card β
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem fixingSubgroup_fixedField [FiniteDimensional F E] : fixingSubgroup (fixedField H) = H := by
  have H_le : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  suffices Nat.card H = Nat.card (fixingSubgroup (fixedField H)) by
    exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
        ⟨Set.inclusion_injective H_le, this⟩).2).symm
  apply Nat.card_congr
  refine (FixedPoints.toAlgHomEquiv H E).trans ?_
  refine (algEquivEquivAlgHom (fixedField H) E).toEquiv.symm.trans ?_
  exact (fixingSubgroupEquiv (fixedField H)).toEquiv.symm

/--
A subgroup is isomorphic to the Galois group of its fixed field.
-/
/-
**IntermediateField.subgroupEquivAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Intermediat
eField`。
形式化陈述：subgroupEquivAlgEquiv [FiniteDimensional F E] (H : Subgroup Gal(E/F)) : H 
≃* Gal(E/IntermediateField.fixedField H)
参数：H : Subgroup Gal(E/F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup is isomorphic to the Galois group of its fixed field.
-/
def subgroupEquivAlgEquiv [FiniteDimensional F E] (H : Subgroup Gal(E/F)) :
    H ≃* Gal(E/IntermediateField.fixedField H) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans (fixingSubgroupEquiv _)
/-
**IntermediateField.fixedField.smul** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField
.fixedField`。
形式化陈述：{F : Type u_1} →   [inst : Field F] →     {E : Type u_2} →       [inst_1 :
 Field E] →         [inst_2 : Algebra F E] → (K : IntermediateField F E) → SMul 
↥K ↥(IntermediateField.fixedField K.fixingSubgroup)
参数：K : IntermediateField F E；IntermediateField.fixedField K.fixingSubgroup。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fixedField.smul : SMul K (fixedField (fixingSubgroup K)) where
  smul x y := ⟨x * y, fun ϕ => by
    rw [smul_mul', show ϕ • (x : E) = ↑x from ϕ.2 x, show ϕ • (y : E) = ↑y from y.2 ϕ]⟩
/-
**IntermediateField.fixedField.algebra** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFi
eld.fixedField`。
形式化陈述：{F : Type u_1} →   [inst : Field F] →     {E : Type u_2} →       [inst_1 :
 Field E] →         [inst_2 : Algebra F E] →           (K : IntermediateField F 
E) → Algebra ↥K ↥(IntermediateField.fixedField K.fixingSubgroup)
参数：K : IntermediateField F E；IntermediateField.fixedField K.fixingSubgroup。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fixedField.algebra : Algebra K (fixedField (fixingSubgroup K)) where
  algebraMap :=
  { toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
    map_zero' := rfl
    map_add' _ _ := rfl
    map_one' := rfl
    map_mul' _ _ := rfl }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl
/-
**IntermediateField.fixedField.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField.fixedField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (K : IntermediateField F E),   IsScalarTower (↥K) (↥(Intermedia
teField.fixedField K.fixingSubgroup)) E
参数：K : IntermediateField F E；↥K；↥(IntermediateField.fixedField K.fixingSubgroup)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance fixedField.isScalarTower : IsScalarTower K (fixedField (fixingSubgroup K)) E :=
  ⟨fun _ _ _ => mul_assoc _ _ _⟩

end IntermediateField

namespace IsGalois

/-- See `InfiniteGalois.fixedField_fixingSubgroup` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption. -/
/-
**IsGalois.fixedField_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：fixedField_fixingSubgroup [FiniteDimensional F E] [h : IsGalois F E] : Int
ermediateField.fixedField (IntermediateField.fixingSubgroup K) = K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.le_iff_le`：le_iff_le : K <= fixedField H ↔ H <= fixing
Subgroup K
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.finrank_fixedField_eq_card`：finrank_fixedField_eq_card
 [FiniteDimensional F E] : finrank (fixedField H) E = Nat.card H
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `IsGalois.tower_top_intermediateField`：∀ {F : Type u_1} {E : Type u_3} [i
nst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K : IntermediateField 
F E)   [IsGalois F E], IsG…
· 使用定理 `IntermediateField.eq_of_le_of_finrank_eq'`：eq_of_le_of_finrank_eq' [Fini
teDimensional F L] (h_le : F <= E) (h_finrank : finrank F L = finrank E L) : F =
 E

--- 原说明 ---
See `InfiniteGalois.fixedField_fixingSubgroup` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption.
-/
theorem fixedField_fixingSubgroup [FiniteDimensional F E] [h : IsGalois F E] :
    IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K := by
  have K_le : K ≤ IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices
    finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_eq' K_le this).symm
  rw [IntermediateField.finrank_fixedField_eq_card,
    Nat.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
  exact (card_aut_eq_finrank K E).symm

/-- See `InfiniteGalois.fixedField_bot` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption. -/
/-
**IsGalois.fixedField_top** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] [IsGalois F E]   [FiniteDimensional F E], IntermediateField.fix
edField ⊤ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.fixingSubgroup_bot`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], ⊥.fixingSubgroup = ⊤
· 使用定理 `IsGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup [FiniteDim
ensional F E] [h : IsGalois F E] : IntermediateField.fixedField (IntermediateFie
ld.fixingSubgroup K) = K

--- 原说明 ---
See `InfiniteGalois.fixedField_bot` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption.
-/
@[simp] lemma fixedField_top [IsGalois F E] [FiniteDimensional F E] :
    fixedField (⊤ : Subgroup Gal(E/F)) = ⊥ := by
  rw [← fixingSubgroup_bot, fixedField_fixingSubgroup]

/-- See `InfiniteGalois.mem_bot_iff_fixed` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption. -/
/-
**IsGalois.mem_bot_iff_fixed** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：mem_bot_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) : x in (⊥
 : IntermediateField F E) ↔ forall f : Gal(E/F), f x = x
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.fixedField_top`：∀ {F : Type u_1} [inst : Field F] {E : Type u_2
} [inst_1 : Field E] [inst_2 : Algebra F E] [IsGalois F E]   [FiniteDimensional 
F E], Interme…
· 使用定理 `IntermediateField.mem_fixedField_iff`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (H : Subgroup Gal(E/F))
   (x : E), x ∈ Intermedia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See `InfiniteGalois.mem_bot_iff_fixed` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption.
-/
theorem mem_bot_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x ∈ (⊥ : IntermediateField F E) ↔ ∀ f : Gal(E/F), f x = x := by
  rw [← fixedField_top, mem_fixedField_iff]
  simp only [Subgroup.mem_top, forall_const]

/-- See `InfiniteGalois.mem_range_algebraMap_iff_fixed` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption. -/
/-
**IsGalois.mem_range_algebraMap_iff_fixed** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：mem_range_algebraMap_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x :
 E) : x in Set.range (algebraMap F E) ↔ forall f : Gal(E/F), f x = x
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.mem_bot_iff_fixed`：mem_bot_iff_fixed [IsGalois F E] [FiniteDime
nsional F E] (x : E) : x in (⊥ : IntermediateField F E) ↔ forall f : Gal(E/F), f
 x = x

--- 原说明 ---
See `InfiniteGalois.mem_range_algebraMap_iff_fixed` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption.
-/
theorem mem_range_algebraMap_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔ ∀ f : Gal(E/F), f x = x :=
  mem_bot_iff_fixed x
/-
**IsGalois.card_fixingSubgroup_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：card_fixingSubgroup_eq_finrank [FiniteDimensional F E] [IsGalois F E] : Na
t.card (IntermediateField.fixingSubgroup K) = finrank K E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup [FiniteDim
ensional F E] [h : IsGalois F E] : IntermediateField.fixedField (IntermediateFie
ld.fixingSubgroup K) = K
· 使用定理 `IntermediateField.finrank_fixedField_eq_card`：finrank_fixedField_eq_card
 [FiniteDimensional F E] : finrank (fixedField H) E = Nat.card H
-/
theorem card_fixingSubgroup_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (IntermediateField.fixingSubgroup K) = finrank K E := by
  conv_rhs => rw [← fixedField_fixingSubgroup K, IntermediateField.finrank_fixedField_eq_card]

/-- The Galois correspondence from intermediate fields to subgroups. -/
@[simps! apply, stacks 09DW]
/-
**IsGalois.intermediateFieldEquivSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `IsGalois`。
形式化陈述：intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] : In
termediateField F E ≃o (Subgroup Gal(E/F))ᵒᵈ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup [FiniteDim
ensional F E] [h : IsGalois F E] : IntermediateField.fixedField (IntermediateFie
ld.fixingSubgroup K) = K
· 使用定理 `IntermediateField.fixingSubgroup_fixedField`：fixingSubgroup_fixedField [
FiniteDimensional F E] : fixingSubgroup (fixedField H) = H

--- 原说明 ---
The Galois correspondence from intermediate fields to subgroups.
-/
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup Gal(E/F))ᵒᵈ where
  toFun := OrderDual.toDual ∘ IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField ∘ OrderDual.ofDual
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L, IntermediateField.le_iff_le, fixedField_fixingSubgroup L]
    rfl

section
variable [FiniteDimensional F E] [IsGalois F E]

/-
**IsGalois.ofDual_intermediateFieldEquivSubgroup_apply** 是 Mathlib 中的一个引理，位于命名空间
 `IsGalois`。
形式化陈述：ofDual_intermediateFieldEquivSubgroup_apply (K : IntermediateField F E) : 
(intermediateFieldEquivSubgroup K).ofDual = K.fixingSubgroup
参数：K : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofDual_intermediateFieldEquivSubgroup_apply (K : IntermediateField F E) :
    (intermediateFieldEquivSubgroup K).ofDual = K.fixingSubgroup := rfl
/-
**IsGalois.intermediateFieldEquivSubgroup_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
IsGalois`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E]   [inst_3 : FiniteDimensional F E] [inst_4 : IsGalois F E] (H :
 (Subgroup Gal(E/F))ᵒᵈ),   IsGalois.intermediateFieldEquivSubgroup.symm H = Inte
rmediateField.fixedField (OrderDual.ofDual H)
参数：H : (Subgroup Gal(E/F))ᵒᵈ；OrderDual.ofDual H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma intermediateFieldEquivSubgroup_symm_apply (H : (Subgroup Gal(E/F))ᵒᵈ) :
    intermediateFieldEquivSubgroup.symm H = fixedField H.ofDual := rfl
/-
**IsGalois.intermediateFieldEquivSubgroup_symm_apply_toDual** 是 Mathlib 中的一个引理，位
于命名空间 `IsGalois`。
形式化陈述：intermediateFieldEquivSubgroup_symm_apply_toDual (H : Subgroup Gal(E/F)) :
 intermediateFieldEquivSubgroup.symm (.toDual H) = fixedField H
参数：H : Subgroup Gal(E/F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma intermediateFieldEquivSubgroup_symm_apply_toDual (H : Subgroup Gal(E/F)) :
    intermediateFieldEquivSubgroup.symm (.toDual H) = fixedField H := rfl
/-
**IsGalois.fixedField_eq_iff_fixingSubgroup_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsGalo
is`。
形式化陈述：fixedField_eq_iff_fixingSubgroup_eq {K : IntermediateField F E} {H : Subgr
oup Gal(E/F)} : fixedField H = K ↔ K.fixingSubgroup = H
参数：E/F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.apply_eq_iff_eq`：apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x =
 e y ↔ x = y
· 使用定理 `IsGalois.intermediateFieldEquivSubgroup_apply`：∀ {F : Type u_1} [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E]   [inst_3 : Fi
niteDimensional F E] [inst_4 : IsGa…
· 使用定理 `IntermediateField.fixingSubgroup_fixedField`：fixingSubgroup_fixedField [
FiniteDimensional F E] : fixingSubgroup (fixedField H) = H
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixedField_eq_iff_fixingSubgroup_eq {K : IntermediateField F E} {H : Subgroup Gal(E/F)} :
    fixedField H = K ↔ K.fixingSubgroup = H := by
  simp [← OrderIso.apply_eq_iff_eq intermediateFieldEquivSubgroup, fixingSubgroup_fixedField,
    eq_comm]

end

/-- The Galois correspondence as a `GaloisInsertion`. -/
/-
**IsGalois.galoisInsertionIntermediateFieldSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `I
sGalois`。
形式化陈述：galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] : GaloisI
nsertion (OrderDual.toDual ∘ (IntermediateField.fixingSubgroup : IntermediateFie
ld F E -> Subgroup Gal(E/F))) ((IntermediateField.fixedField : Subgroup Gal(E/F)
 -> IntermediateField F E) ∘ OrderDual.toDual) where choice K _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois correspondence as a `GaloisInsertion`.
-/
def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup Gal(E/F)))
      ((IntermediateField.fixedField : Subgroup Gal(E/F) → IntermediateField F E) ∘
        OrderDual.toDual) where
  choice K _ := IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl

/-- The Galois correspondence as a `GaloisCoinsertion`. -/
/-
**IsGalois.galoisCoinsertionIntermediateFieldSubgroup** 是 Mathlib 中的一个定义，位于命名空间 
`IsGalois`。
形式化陈述：galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalo
is F E] : GaloisCoinsertion (OrderDual.toDual ∘ (IntermediateField.fixingSubgrou
p : IntermediateField F E -> Subgroup Gal(E/F))) ((IntermediateField.fixedField 
: Subgroup Gal(E/F) -> IntermediateField F E) ∘ OrderDual.toDual)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois correspondence as a `GaloisCoinsertion`.
-/
def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup Gal(E/F)))
      ((IntermediateField.fixedField : Subgroup Gal(E/F) → IntermediateField F E) ∘
        OrderDual.toDual) :=
  OrderIso.toGaloisCoinsertion intermediateFieldEquivSubgroup

end IsGalois

section

/-In this section we prove that the normal subgroups correspond to the Galois subextensions
in the Galois correspondence and its related results. -/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open IntermediateField

open scoped Pointwise

/-
**IntermediateField.restrictNormalHom_ker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IntermediateField.restrictNormalHom_ker (E : IntermediateField K L) [Norma
l K E] : (restrictNormalHom E).ker = E.fixingSubgroup
参数：E : IntermediateField K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.one_apply`：one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgEquiv.restrictNormalHom_apply`：AlgEquiv.restrictNormalHom_apply (L : 
IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F)) (x : L) : restrictNormalHom
 L σ x = σ x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IntermediateField.restrictNormalHom_ker (E : IntermediateField K L) [Normal K E] :
    (restrictNormalHom E).ker = E.fixingSubgroup := by
  simp only [Subgroup.ext_iff, MonoidHom.mem_ker, AlgEquiv.ext_iff, one_apply, Subtype.ext_iff,
    restrictNormalHom_apply, Subtype.forall, mem_fixingSubgroup_iff, implies_true]

namespace IsGalois

variable (E : IntermediateField K L)

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `fixedField H` is Galois over `K`. -/
/-
**IsGalois.of_fixedField_normal_subgroup** 是 Mathlib 中的一个实例，位于命名空间 `IsGalois`。
形式化陈述：of_fixedField_normal_subgroup [IsGalois K L] (H : Subgroup Gal(L/K)) [hn :
 Subgroup.Normal H] : IsGalois K (fixedField H) where to_isSeparable
参数：H : Subgroup Gal(L/K)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IntermediateField.normal_iff_forall_map_le'`：normal_iff_forall_map_le' :
 Normal F K ↔ forall σ : Gal(L/F), K.map ↑σ <= K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
· 使用定理 `Subgroup.Normal.conj_mem'`：conj_mem' (nH : H.Normal) (n : G) (hn : n in 
H) (g : G) : g⁻¹ * n * g in H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `H` is a normal Subgroup of `Gal(L / K)`, then `fixedField H` is Galois over 
`K`.
-/
instance of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup Gal(L/K)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply normal_iff_forall_map_le'.mpr
    rintro σ x ⟨a, ha, rfl⟩ τ
    exact (symm_apply_eq σ).mp (ha ⟨σ⁻¹ * τ * σ, Subgroup.Normal.conj_mem' hn τ.1 τ.2 σ⟩)

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `Gal(fixedField H / K)` is isomorphic to
`Gal(L / K) ⧸ H`. -/
/-
**IsGalois.normalAutEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `IsGalois`。
形式化陈述：normalAutEquivQuotient [FiniteDimensional K L] [IsGalois K L] (H : Subgrou
p Gal(L/K)) [Subgroup.Normal H] : Gal(L/K) ⧸ H ≃* Gal(fixedField H/K)
参数：H : Subgroup Gal(L/K)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H` is a normal Subgroup of `Gal(L / K)`, then `Gal(fixedField H / K)` is iso
morphic to
`Gal(L / K) ⧸ H`.
-/
noncomputable def normalAutEquivQuotient [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [Subgroup.Normal H] :
    Gal(L/K) ⧸ H ≃* Gal(fixedField H/K) :=
  QuotientGroup.liftEquiv _ (restrictNormalHom_surjective L) <|
    (fixingSubgroup_fixedField H).symm.trans (fixedField H).restrictNormalHom_ker.symm
/-
**IsGalois.normalAutEquivQuotient_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsGalois`。
形式化陈述：normalAutEquivQuotient_apply [FiniteDimensional K L] [IsGalois K L] (H : S
ubgroup Gal(L/K)) [Subgroup.Normal H] (σ : Gal(L/K)) : normalAutEquivQuotient H 
σ = (restrictNormalHom (fixedField H)) σ
参数：H : Subgroup Gal(L/K)；σ : Gal(L/K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma normalAutEquivQuotient_apply [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [Subgroup.Normal H] (σ : Gal(L/K)) :
    normalAutEquivQuotient H σ = (restrictNormalHom (fixedField H)) σ := rfl

open scoped Pointwise

@[simp]
/-
**IsGalois.map_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：map_fixingSubgroup (σ : Gal(L/K)) : (E.map σ).fixingSubgroup = (MulAut.con
j σ) • E.fixingSubgroup
参数：σ : Gal(L/K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_fixingSubgroup (σ : Gal(L/K)) :
    (E.map σ).fixingSubgroup = (MulAut.conj σ) • E.fixingSubgroup := by
  ext τ
  simp only [coe_map, AlgEquiv.coe_toAlgHom, Set.mem_image, SetLike.mem_coe, AlgEquiv.smul_def,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← symm_apply_eq,
    IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
  rfl

/-- Let `E` be an intermediateField of a Galois extension `L / K`. If `E / K` is
Galois extension, then `E.fixingSubgroup` is a normal subgroup of `Gal(L / K)`. -/
/-
**IsGalois.fixingSubgroup_normal_of_isGalois** 是 Mathlib 中的一个实例，位于命名空间 `IsGalois
`。
形式化陈述：fixingSubgroup_normal_of_isGalois [IsGalois K L] [IsGalois K E] : E.fixing
Subgroup.Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.of_conjugate_fixed`：∀ {G : Type u_2} [inst : Group G] {H
 : Subgroup G}, (∀ (g : G), MulAut.conj g • H = H) → H.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.map_fixingSubgroup`：map_fixingSubgroup (σ : Gal(L/K)) : (E.map 
σ).fixingSubgroup = (MulAut.conj σ) • E.fixingSubgroup
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IntermediateField.normal_iff_forall_map_eq'`：normal_iff_forall_map_eq' :
 Normal F K ↔ forall σ : Gal(L/F), K.map ↑σ = K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E

--- 原说明 ---
Let `E` be an intermediateField of a Galois extension `L / K`. If `E / K` is
Galois extension, then `E.fixingSubgroup` is a normal subgroup of `Gal(L / K)`.
-/
instance fixingSubgroup_normal_of_isGalois [IsGalois K L] [IsGalois K E] :
    E.fixingSubgroup.Normal := by
  apply Subgroup.Normal.of_conjugate_fixed (fun σ ↦ ?_)
  rw [← map_fixingSubgroup, normal_iff_forall_map_eq'.mp inferInstance σ]

end IsGalois

end

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

namespace IsGalois

/-
**IsGalois.is_separable_splitting_field** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] : exis
ts p : F[X], p.Separable ∧ p.IsSplittingField F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.exists_primitive_element`：exists_primitive_element : exists α : E,
 F⟮α⟯ = ⊤
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsGalois.separable`：separable [IsGalois F E] (x : E) : IsSeparable F x
· 使用定理 `IsGalois.splits`：splits [IsGalois F E] (x : E) : ((minpoly F x).map (alg
ebraMap F E)).Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.top_toSubalgebra`：top_toSubalgebra : (⊤ : Intermediate
Field F E).toSubalgebra = ⊤
· 使用定理 `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`：adjoin_simp
le_toSubalgebra_of_isAlgebraic (hα : IsAlgebraic F α) : F⟮α⟯.toSubalgebra = F[α]
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.integral`：integral [IsGalois F E] (x : E) : IsIntegral F x
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E := by
  obtain ⟨α, h1⟩ := Field.exists_primitive_element F E
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← h1]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (integral F α).isAlgebraic]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
  exact ⟨minpoly.ne_zero (integral F α), minpoly.aeval _ _⟩
/-
**IsGalois.of_fixedField_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：of_fixedField_eq_bot [FiniteDimensional F E] (h : IntermediateField.fixedF
ield (⊤ : Subgroup Gal(E/F)) = ⊥) : IsGalois F E
参数：h : IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isGalois_iff_isGalois_bot`：isGalois_iff_isGalois_bot : IsGalois (⊥ : Int
ermediateField F E) E ↔ IsGalois F E
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
-/
theorem of_fixedField_eq_bot [FiniteDimensional F E]
    (h : IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥) : IsGalois F E := by
  rw [← isGalois_iff_isGalois_bot, ← h]
  exact IsGalois.of_fixed_field E (⊤ : Subgroup Gal(E/F))

/-- Let $E / F$ be a finite extension of fields. If $|\text{Aut}(E/F)| = [E : F]$, then
$E$ is Galois over $F$. -/
@[stacks 09I1 "'if' part"]
/-
**IsGalois.of_card_aut_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：of_card_aut_eq_finrank [FiniteDimensional F E] (h : Nat.card Gal(E/F) = fi
nrank F E) : IsGalois F E
参数：h : Nat.card Gal(E/F) = finrank F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.of_fixedField_eq_bot`：of_fixedField_eq_bot [FiniteDimensional F
 E] (h : IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥) : IsGalois F 
E
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
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
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.finrank_eq_one_iff`：finrank_eq_one_iff : finrank F K =
 1 ↔ K = ⊥
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IntermediateField.finrank_fixedField_eq_card`：finrank_fixedField_eq_card
 [FiniteDimensional F E] : finrank (fixedField H) E = Nat.card H
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)

--- 原说明 ---
Let $E / F$ be a finite extension of fields. If $|\text{Aut}(E/F)| = [E : F]$, t
hen
$E$ is Galois over $F$.
-/
theorem of_card_aut_eq_finrank [FiniteDimensional F E]
    (h : Nat.card Gal(E/F) = finrank F E) : IsGalois F E := by
  apply of_fixedField_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup Gal(E/F))) E := finrank_pos
  rw [← IntermediateField.finrank_eq_one_iff, ← mul_left_inj' (ne_of_lt p).symm,
    finrank_mul_finrank, ← h, one_mul, IntermediateField.finrank_fixedField_eq_card]
  apply Nat.card_congr
  exact { toFun := fun g => ⟨g, Subgroup.mem_top g⟩, invFun := (↑) }

variable {F} {E}
variable {p : F[X]}

@[deprecated "No replacement; this was an auxiliary lemma used to prove \
`Algebra.isSeparable_of_separable_splitting_field`." (since := "2026-06-12")]
/-
**IsGalois.of_separable_splitting_field_aux** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`
。
形式化陈述：of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.IsS
plittingField F E] (hp : p.Separable) (K : Type*) [Field K] [Algebra F K] [Algeb
ra K E] [IsScalarTower F K E] {x : E} (hx : x in p.aroots E) : Nat.card (K⟮x⟯.re
strictScalars F ->ₐ[F] E) = Nat.card (K ->ₐ[F] E) * finrank K K⟮x⟯
参数：hp : p.Separable；K : Type*；hx : x in p.aroots E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `isIntegral_of_noetherian`：isIntegral_of_noetherian (_ : IsNoetherian R B
) (x : B) : IsIntegral R x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsNoetherian.iff_fg`：iff_fg : IsNoetherian K V ↔ Module.Finite K V
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_zero`：aroots_zero (S) [CommRing S] [IsDomain S] [Algeb
ra T S] : (0 : T[X]).aroots S = 0
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd
（共 49 条，此处仅展示前 30 条）
-/
theorem of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.IsSplittingField F E]
    (hp : p.Separable) (K : Type*) [Field K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    {x : E} (hx : x ∈ p.aroots E) :
    Nat.card (K⟮x⟯.restrictScalars F →ₐ[F] E) = Nat.card (K →ₐ[F] E) * finrank K K⟮x⟯ := by
  have h : IsIntegral K x := (isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x).tower_top
  have h1 : p ≠ 0 := fun hp => by
    rw [hp, Polynomial.aroots_zero] at hx
    exact Multiset.notMem_zero x hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← Polynomial.eval_map, ←
      IsScalarTower.algebraMap_eq]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero h1)).mp hx
  let key_equiv : (K⟮x⟯.restrictScalars F →ₐ[F] E) ≃
      Σ f : K →ₐ[F] E, @AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f) := by
    change (K⟮x⟯ →ₐ[F] E) ≃ Σ f : K →ₐ[F] E, _
    exact algHomEquivSigma
  have : ∀ f : K →ₐ[F] E, Finite (@AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f)) := fun f => by
    have := Finite.of_equiv _ key_equiv
    apply Finite.of_injective (Sigma.mk f) fun _ _ H => eq_of_heq (Sigma.ext_iff.mp H).2
  have : FiniteDimensional F K := FiniteDimensional.left F K E
  rw [Nat.card_congr key_equiv, Nat.card_sigma, IntermediateField.adjoin.finrank h,
    Nat.card_eq_fintype_card]
  apply Finset.sum_const_nat
  intro f _
  rw [← @IntermediateField.card_algHom_adjoin_integral K _ E _ _ x E _ (RingHom.toAlgebra f) h]
  · exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap F K)).mpr hp) h2
  · apply sp.splits.of_dvd (Polynomial.map_ne_zero h1)
    rwa [← f.comp_algebraMap, ← p.map_map, RingHom.algebraMap_toAlgebra, Polynomial.map_dvd_map']
/-
**IsGalois.of_separable_splitting_field** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：of_separable_splitting_field [p.IsSplittingField F E] (hp : p.Separable) :
 IsGalois F E
参数：hp : p.Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isSeparable_of_separable_splitting_field`：Algebra.isSeparable_of
_separable_splitting_field {p : F[X]} [sp : p.IsSplittingField F E] (hp : p.Sepa
rable) : Algebra.IsSeparable F E
· 使用定理 `Normal.of_isSplittingField`：Normal.of_isSplittingField (p : F[X]) [hFEp 
: IsSplittingField F E p] : Normal F E
-/
theorem of_separable_splitting_field [p.IsSplittingField F E] (hp : p.Separable) :
    IsGalois F E :=
  { to_isSeparable := Algebra.isSeparable_of_separable_splitting_field F E hp,
    to_normal := Normal.of_isSplittingField p }

/-- Equivalent characterizations of a Galois extension of finite degree. -/
/-
**IsGalois.tfae** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：tfae [FiniteDimensional F E] : List.TFAE [ IsGalois F E, IntermediateField
.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥, Nat.card Gal(E/F) = finrank F E, exists
 p : F[X], p.Separable ∧ p.IsSplittingField F E]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `IsGalois.is_separable_splitting_field`：is_separable_splitting_field [Fin
iteDimensional F E] [IsGalois F E] : exists p : F[X], p.Separable ∧ p.IsSplittin
gField F E
· 使用定理 `IsGalois.of_fixedField_eq_bot`：of_fixedField_eq_bot [FiniteDimensional F
 E] (h : IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥) : IsGalois F 
E
· 使用定理 `IsGalois.of_card_aut_eq_finrank`：of_card_aut_eq_finrank [FiniteDimension
al F E] (h : Nat.card Gal(E/F) = finrank F E) : IsGalois F E
· 使用定理 `IsGalois.of_separable_splitting_field`：of_separable_splitting_field [p.I
sSplittingField F E] (hp : p.Separable) : IsGalois F E
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
Equivalent characterizations of a Galois extension of finite degree.
-/
theorem tfae [FiniteDimensional F E] : List.TFAE [
    IsGalois F E,
    IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥,
    Nat.card Gal(E/F) = finrank F E,
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E] := by
  tfae_have 1 → 2 := fun h ↦ OrderIso.map_bot (@intermediateFieldEquivSubgroup F _ E _ _ _ h).symm
  tfae_have 1 → 3 := fun _ ↦ card_aut_eq_finrank F E
  tfae_have 1 → 4 := fun _ ↦ is_separable_splitting_field F E
  tfae_have 2 → 1 := of_fixedField_eq_bot F E
  tfae_have 3 → 1 := of_card_aut_eq_finrank F E
  tfae_have 4 → 1 := fun ⟨h, hp1, _⟩ ↦ of_separable_splitting_field hp1
  tfae_finish

/--
If `K/F` is a finite Galois extension, then for any extension `L/F`, the extension `KL/L`
is also Galois.
-/
/-
**IsGalois.sup_right** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois`。
形式化陈述：sup_right (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional 
F K] (h : K ⊔ L = ⊤) : IsGalois L E
参数：K L : IntermediateField F E；h : K ⊔ L = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.is_separable_splitting_field`：is_separable_splitting_field [Fin
iteDimensional F E] [IsGalois F E] : exists p : F[X], p.Separable ∧ p.IsSplittin
gField F E
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSplittingField_iff_intermediateField`：isSplittingField_iff_intermediat
eField : p.IsSplittingField K L ↔ (p.map (algebraMap K L)).Splits ∧ Intermediate
Field.adjoin K (p.rootSet L)…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.Splits.of_algHom`：∀ {R : Type u_1} [inst : CommSemiring R] {f
 : Polynomial R} {A : Type u_2} {B : Type u_3} [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [ins…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IntermediateField.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff
 {L : IntermediateField F E} : L.restrictScalars K = ⊤ ↔ L = ⊤
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `IntermediateField.adjoin_union`：adjoin_union {S T : Set E} : adjoin F (S
 union T) = adjoin F S ⊔ adjoin F T
· 使用定理 `IntermediateField.adjoin_self`：adjoin_self (K : IntermediateField F E) :
 adjoin F K = K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.Splits.image_rootSet`：∀ {R : Type u_1} {A : Type u_2} {B : Ty
pe u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A]   [inst_3 
: CommRing B] [inst_4…
· 使用定理 `IntermediateField.coe_val`：coe_val : ⇑S.val = ((↑) : S -> L)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `K/F` is a finite Galois extension, then for any extension `L/F`, the extensi
on `KL/L`
is also Galois.
-/
theorem sup_right (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K]
    (h : K ⊔ L = ⊤) : IsGalois L E := by
  obtain ⟨T, hT₁, hT₂⟩ := IsGalois.is_separable_splitting_field F K
  let T' := T.map (algebraMap F L)
  suffices T'.IsSplittingField L E from IsGalois.of_separable_splitting_field (p := T') hT₁.map
  rw [isSplittingField_iff_intermediateField] at hT₂ ⊢
  constructor
  · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact Polynomial.Splits.of_algHom hT₂.1 (IsScalarTower.toAlgHom _ _ _)
  · have h' : T'.rootSet E = T.rootSet E := by simp [Set.ext_iff, Polynomial.mem_rootSet', T']
    rw [← lift_inj, lift_adjoin, ← coe_val, hT₂.1.image_rootSet] at hT₂
    rw [← restrictScalars_eq_top_iff (K := F), restrictScalars_adjoin, adjoin_union, adjoin_self,
      h', hT₂.2, lift_top, sup_comm, h]

end IsGalois

end GaloisEquivalentDefinitions

section normalClosure

variable (k K F : Type*) [Field k] [Field K] [Field F] [Algebra k K] [Algebra k F] [Algebra K F]
  [IsScalarTower k K F] [IsGalois k F]

/-- Let $F / K / k$ be a tower of field extensions. If $F$ is Galois over $k$,
then the normal closure of $K$ over $k$ in $F$ is Galois over $k$. -/
@[stacks 0EXM]
/-
**IsGalois.normalClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsGalois.normalClosure : IsGalois k (normalClosure k K F) where to_isSepar
able
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E

--- 原说明 ---
Let $F / K / k$ be a tower of field extensions. If $F$ is Galois over $k$,
then the normal closure of $K$ over $k$ in $F$ is Galois over $k$.
-/
instance IsGalois.normalClosure : IsGalois k (normalClosure k K F) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable k _ F

end normalClosure

section IsAlgClosure

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsAlgClosure.isGalois (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosure k K] [CharZero k] : IsGalois k K where

end IsAlgClosure


section restrictRestrictAlgEquivMapHom

namespace IntermediateField

/--
The map from the `Gal(E/L)` to `Gal(K/F)` where `E/L/F` and `E/K/F` are two towers of
extensions induced by the restriction to `K`. Note that we do require `K/F` to be normal but not
`E/L`. If this is the case (and everything is finite dimensional) and `K ∩ L = F` then this
map is surjective, see `IntermediateField.restrictRestrictMapHom_surjective`.
This map is injective if the compositum of `K` and `L` is `E`,
see `IntermediateField.restrictRestrictAlgEquivMapHom_injective`.
-/
/-
**IntermediateField.restrictRestrictAlgEquivMapHom** 是 Mathlib 中的一个定义，位于命名空间 `In
termediateField`。
形式化陈述：restrictRestrictAlgEquivMapHom (F K L E : Type*) [Field F] [Field K] [Fiel
d L] [Field E] [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra 
L E] [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] : Gal(E/L) ->* Gal
(K/F)
参数：F K L E : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the `Gal(E/L)` to `Gal(K/F)` where `E/L/F` and `E/K/F` are two towe
rs of
extensions induced by the restriction to `K`. Note that we do require `K/F` to b
e normal but not
`E/L`. If this is the case (and everything is finite dimensional) and `K ∩ L = F
` then this
map is surjective, see `IntermediateField.restrictRestrictMapHom_surjective`.
This map is injective if the compositum of `K` and `L` is `E`,
see `IntermediateField.restrictRestrictAlgEquivMapHom_injective`.
-/
noncomputable def restrictRestrictAlgEquivMapHom (F K L E : Type*) [Field F] [Field K] [Field L]
    [Field E] [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] :
    Gal(E/L) →* Gal(K/F) :=
  (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut Gal(E/L) F E)

variable {F E : Type*} (E' : Type*) [Field F] [Field E] [Field E']
  [Algebra F E] [Algebra F E'] [Algebra E E'] [IsScalarTower F E E']
  (K L : IntermediateField F E) [Normal F K]

@[simp]
/-
**IntermediateField.restrictRestrictAlgEquivMapHom_apply** 是 Mathlib 中的一个定理，位于命名
空间 `IntermediateField`。
形式化陈述：restrictRestrictAlgEquivMapHom_apply (φ : Gal(E/L)) (x : K) : restrictRest
rictAlgEquivMapHom F K L E φ x = φ x
参数：φ : Gal(E/L)；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulSemiringAction.toAlgAut_apply`：∀ (G : Type u_2) (R : Type u_3) (A : T
ype u_4) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   
[inst_3 : Group G] [in…
· 使用引理 `AlgEquiv.restrictNormalHom_apply`：AlgEquiv.restrictNormalHom_apply (L : 
IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F)) (x : L) : restrictNormalHom
 L σ x = σ x
· 使用定理 `MulSemiringAction.toAlgEquiv_apply`：∀ {G : Type u_2} (R : Type u_3) (A :
 Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  [inst_3 : Group G] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrictRestrictAlgEquivMapHom_apply (φ : Gal(E/L)) (x : K) :
    restrictRestrictAlgEquivMapHom F K L E φ x = φ x := by
  simp [restrictRestrictAlgEquivMapHom, AlgEquiv.restrictNormalHom_apply]
/-
**IntermediateField.restrictRestrictAlgEquivMapHom_injective** 是 Mathlib 中的一个定理，
位于命名空间 `IntermediateField`。
形式化陈述：restrictRestrictAlgEquivMapHom_injective (h : K ⊔ L = ⊤) : Function.Inject
ive (restrictRestrictAlgEquivMapHom F K L E)
参数：h : K ⊔ L = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `IntermediateField.fixingSubgroup_top`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], ⊤.fixingSubgroup = ⊥
· 使用定理 `IntermediateField.fixingSubgroup_sup`：fixingSubgroup_sup {K L : Intermed
iateField F E} : (K ⊔ L).fixingSubgroup = K.fixingSubgroup ⊓ L.fixingSubgroup
· 使用定理 `IntermediateField.restrictRestrictAlgEquivMapHom_apply`：restrictRestrict
AlgEquivMapHom_apply (φ : Gal(E/L)) (x : K) : restrictRestrictAlgEquivMapHom F K
 L E φ x = φ x
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
-/
theorem restrictRestrictAlgEquivMapHom_injective (h : K ⊔ L = ⊤) :
    Function.Injective (restrictRestrictAlgEquivMapHom F K L E) := by
  refine (injective_iff_map_eq_one _).mpr fun φ hφ ↦ ?_
  suffices h : MulSemiringAction.toAlgAut Gal(E/L) F E φ = 1 by rwa [AlgEquiv.ext_iff] at h ⊢
  rw [← Subgroup.mem_bot, ← fixingSubgroup_top, ← h, fixingSubgroup_sup]
  exact ⟨fun x ↦ (hφ ▸ restrictRestrictAlgEquivMapHom_apply K L φ x).symm, φ.commutes⟩
/-
**IntermediateField.restrictRestrictAlgEquivMapHom_surjective** 是 Mathlib 中的一个定理
，位于命名空间 `IntermediateField`。
形式化陈述：restrictRestrictAlgEquivMapHom_surjective [FiniteDimensional F K] [FiniteD
imensional L E] [IsGalois L E] (h : K ⊓ L = ⊥) : Function.Surjective (restrictRe
strictAlgEquivMapHom F K L E)
参数：h : K ⊓ L = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `IsGalois.mem_bot_iff_fixed`：mem_bot_iff_fixed [IsGalois F E] [FiniteDime
nsional F E] (x : E) : x in (⊥ : IntermediateField F E) ↔ forall f : Gal(E/F), f
 x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.restrictRestrictAlgEquivMapHom_apply`：restrictRestrict
AlgEquivMapHom_apply (φ : Gal(E/L)) (x : K) : restrictRestrictAlgEquivMapHom F K
 L E φ x = φ x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IntermediateField.mem_fixedField_iff`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (H : Subgroup Gal(E/F))
   (x : E), x ∈ Intermedia…
· 使用定理 `IntermediateField.mem_inf`：mem_inf {S T : IntermediateField F E} {x : E}
 : x in S ⊓ T ↔ x in S ∧ x in T
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `IntermediateField.fixingSubgroup_bot`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], ⊥.fixingSubgroup = ⊤
· 使用定理 `IntermediateField.fixingSubgroup_fixedField`：fixingSubgroup_fixedField [
FiniteDimensional F E] : fixingSubgroup (fixedField H) = H
-/
theorem restrictRestrictAlgEquivMapHom_surjective [FiniteDimensional F K] [FiniteDimensional L E]
    [IsGalois L E] (h : K ⊓ L = ⊥) :
    Function.Surjective (restrictRestrictAlgEquivMapHom F K L E) := by
  suffices fixedField (restrictRestrictAlgEquivMapHom F K L E).range = ⊥ from
     MonoidHom.range_eq_top.mp <|
      fixingSubgroup_fixedField (restrictRestrictAlgEquivMapHom F K L E).range ▸
        this ▸ fixingSubgroup_bot
  refine eq_bot_iff.mpr fun ⟨x, hx₁⟩ hx₂ ↦ ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ : x ∈ Set.range (algebraMap L E) := by
    refine mem_bot.mp <| (IsGalois.mem_bot_iff_fixed _).mpr fun φ ↦ ?_
    rw [← restrictRestrictAlgEquivMapHom_apply K L φ ⟨x, hx₁⟩]
    rw [mem_fixedField_iff] at hx₂
    exact congr_arg ((↑) : K → E) <| hx₂ (restrictRestrictAlgEquivMapHom F K L E φ) ⟨φ, rfl⟩
  obtain ⟨z, rfl⟩ : y ∈ (⊥ : IntermediateField F E) := h ▸ mem_inf.mpr ⟨hx₁, hy⟩
  exact mem_bot.mp ⟨z, rfl⟩

/-- If `K / E / k` is a field extension tower with `E / k` normal,
`L` is an intermediate field of `E / k`, then the fixing subgroup of `L` viewed as an
intermediate field of `K / k` is equal to the preimage of the fixing subgroup of `L` viewed as an
intermediate field of `E / k` under the natural map `Aut(K / k) → Aut(E / k)`
(`AlgEquiv.restrictNormalHom`). -/
/-
**IntermediateField.map_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：map_fixingSubgroup [Normal F E] : (L.map (IsScalarTower.toAlgHom F E E')).
fixingSubgroup = L.fixingSubgroup.comap (AlgEquiv.restrictNormalHom (F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)

--- 原说明 ---
If `K / E / k` is a field extension tower with `E / k` normal,
`L` is an intermediate field of `E / k`, then the fixing subgroup of `L` viewed 
as an
intermediate field of `K / k` is equal to the preimage of the fixing subgroup of
 `L` viewed as an
intermediate field of `E / k` under the natural map `Aut(K / k) → Aut(E / k)`
(`AlgEquiv.restrictNormalHom`).
-/
theorem map_fixingSubgroup [Normal F E] :
    (L.map (IsScalarTower.toAlgHom F E E')).fixingSubgroup =
      L.fixingSubgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := E') E) := by
  ext f
  simp only [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  constructor
  · rintro h x hx
    change f.restrictNormal E x = x
    apply_fun _ using (algebraMap E E').injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    replace h := congr(algebraMap E E' $(show f.restrictNormal E x = x from h x hx))
    rwa [AlgEquiv.restrictNormal_commutes] at h

/-- If `K / E / k` is a field extension tower with `E / k` and `K / k` normal,
`L` is an intermediate field of `E / k`, then the index of the fixing subgroup of `L` viewed as an
intermediate field of `K / k` is equal to the index of the fixing subgroup of `L` viewed as an
intermediate field of `E / k`. -/
/-
**IntermediateField.map_fixingSubgroup_index** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：map_fixingSubgroup_index [Normal F E] [Normal F E'] : (L.map (IsScalarTowe
r.toAlgHom F E E')).fixingSubgroup.index = L.fixingSubgroup.index
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.map_fixingSubgroup`：map_fixingSubgroup [Normal F E] : 
(L.map (IsScalarTower.toAlgHom F E E')).fixingSubgroup = L.fixingSubgroup.comap 
(AlgEquiv.restrictNormalHo…
· 使用定理 `Subgroup.index_comap_of_surjective`：index_comap_of_surjective {f : G' ->
* G} (hf : Function.Surjective f) : (H.comap f).index = H.index
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…

--- 原说明 ---
If `K / E / k` is a field extension tower with `E / k` and `K / k` normal,
`L` is an intermediate field of `E / k`, then the index of the fixing subgroup o
f `L` viewed as an
intermediate field of `K / k` is equal to the index of the fixing subgroup of `L
` viewed as an
intermediate field of `E / k`.
-/
theorem map_fixingSubgroup_index [Normal F E] [Normal F E'] :
    (L.map (IsScalarTower.toAlgHom F E E')).fixingSubgroup.index = L.fixingSubgroup.index := by
  rw [L.map_fixingSubgroup E', L.fixingSubgroup.index_comap_of_surjective
    (AlgEquiv.restrictNormalHom_surjective _)]

variable {K} in
/-- If `K / k` is a Galois extension, `L` is an intermediate field of `K / k`, then `[L : k]`
as a natural number is equal to the index of the fixing subgroup of `L`. -/
/-
**IntermediateField.finrank_eq_fixingSubgroup_index** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：finrank_eq_fixingSubgroup_index (L : IntermediateField F E') [IsGalois F E
'] : Module.finrank F L = L.fixingSubgroup.index
参数：L : IntermediateField F E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.fieldRange_val`：fieldRange_val : S.val.fieldRange = S
· 使用引理 `AlgHom.fieldRange_le_normalClosure`：AlgHom.fieldRange_le_normalClosure (
f : K ->ₐ[F] L) : f.fieldRange <= normalClosure F K L
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Nat.mul_left_inj`：∀ {a b c : ℕ}, a ≠ 0 → (b * a = c * a ↔ b = c)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finite.card_pos`：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.c
ard α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.index_mul_card`：index_mul_card : H.index * Nat.card H = Nat.car
d G
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `IsGalois.card_fixingSubgroup_eq_finrank`：card_fixingSubgroup_eq_finrank 
[FiniteDimensional F E] [IsGalois F E] : Nat.card (IntermediateField.fixingSubgr
oup K) = finrank K E
· 使用定理 `IntermediateField.map_fixingSubgroup_index`：map_fixingSubgroup_index [No
rmal F E] [Normal F E'] : (L.map (IsScalarTower.toAlgHom F E E')).fixingSubgroup
.index = L.fixingSubgroup.index
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `IntermediateField.lift_restrict`：lift_restrict : lift (restrict h) = F
· 使用定理 `Module.finrank_of_infinite_dimensional`：finrank_of_infinite_dimensional 
(h : ¬FiniteDimensional K V) : finrank K V = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `K / k` is a Galois extension, `L` is an intermediate field of `K / k`, then 
`[L : k]`
as a natural number is equal to the index of the fixing subgroup of `L`.
-/
theorem finrank_eq_fixingSubgroup_index (L : IntermediateField F E') [IsGalois F E'] :
    Module.finrank F L = L.fixingSubgroup.index := by
  wlog hnfd : FiniteDimensional F L generalizing L
  · rw [Module.finrank_of_infinite_dimensional hnfd]
    by_contra! h
    replace h : L.fixingSubgroup.FiniteIndex := ⟨h.symm⟩
    obtain ⟨L', hfd, hL'⟩ :=
      exists_lt_finrank_of_infinite_dimensional hnfd L.fixingSubgroup.index
    let i := (liftAlgEquiv L').toLinearEquiv
    replace hfd := i.finiteDimensional
    rw [i.finrank_eq, this _ hfd] at hL'
    exact (Subgroup.index_antitone <| fixingSubgroup_le <|
      IntermediateField.lift_le L').not_gt hL'
  let E := normalClosure F L E'
  have hle : L ≤ E := by simpa only [fieldRange_val] using L.val.fieldRange_le_normalClosure
  let L' := restrict hle
  have h := Module.finrank_mul_finrank F ↥L' ↥E
  classical
  rw [← IsGalois.card_fixingSubgroup_eq_finrank L', ← IsGalois.card_aut_eq_finrank F E] at h
  rw [← L'.fixingSubgroup.index_mul_card, Nat.mul_left_inj Finite.card_pos.ne'] at h
  rw [(restrictAlgEquiv hle).toLinearEquiv.finrank_eq, h, ← L'.map_fixingSubgroup_index E']
  congr 2
  exact lift_restrict hle

end IntermediateField

end restrictRestrictAlgEquivMapHom

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [IsQuadraticExtension F K]

/--
A quadratic separable extension is Galois.
-/
/-
**Algebra.IsQuadraticExtension.isGalois** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsQua
draticExtension`。
形式化陈述：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst_
2 : Algebra F K]   [Algebra.IsQuadraticExtension F K] [Algebra.IsSeparable F K],
 IsGalois F K
参数：F : Type u_1；K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
A quadratic separable extension is Galois.
-/
instance IsQuadraticExtension.isGalois [Algebra.IsSeparable F K] : IsGalois F K where

/--
A quadratic extension has cyclic Galois group.
-/
/-
**Algebra.IsQuadraticExtension.isCyclic** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsQua
draticExtension`。
形式化陈述：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst_
2 : Algebra F K]   [Algebra.IsQuadraticExtension F K], IsCyclic Gal(K/F)
参数：F : Type u_1；K : Type u_2；K/F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.instFiniteOfIsQuadraticExtension`：∀ (R : Type u_2) (S : Type u_3
) [inst : CommSemiring R] [inst_1 : StrongRankCondition R] [inst_2 : Semiring S]
   [inst_3 : Algebra R S] [Alg…
· 使用定理 `AlgEquiv.card_le`：AlgEquiv.card_le {F K : Type*} [Field F] [Field K] [Al
gebra F K] [FiniteDimensional F K] : Fintype.card Gal(K/F) <= Module.finrank F K
· 使用定理 `Algebra.IsQuadraticExtension.finrank_eq_two`：∀ (R : Type u_2) (S : Type 
u_3) [inst : CommSemiring R] [inst_1 : StrongRankCondition R] [inst_2 : Semiring
 S]   [inst_3 : Algebra R S] [Alg…
· 使用定理 `isCyclic_of_prime_card`：isCyclic_of_prime_card {p : Nat} [hp : Fact p.Pr
ime] (h : Nat.card α = p) : IsCyclic α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_right`：of_le_right [LE α] (h : (a : α
) <= b) (eq : b = b') : a <= b'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `isCyclic_of_subsingleton`：∀ {α : Type u_1} [inst : Group α] [Subsingleto
n α], IsCyclic α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton [Finit
e α] : Nat.card α <= 1 ↔ Subsingleton α
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
A quadratic extension has cyclic Galois group.
-/
instance IsQuadraticExtension.isCyclic : IsCyclic Gal(K/F) := by
  have := finrank_eq_two F K ▸ AlgEquiv.card_le
  rw [← Nat.card_eq_fintype_card] at this
  interval_cases h : Nat.card Gal(K/F)
  · simp_all
  · exact @isCyclic_of_subsingleton _ _ (Finite.card_le_one_iff_subsingleton.mp h.le)
  · exact isCyclic_of_prime_card h

@[deprecated inferInstance (since := "2026-04-09")]
/-
**Algebra.IsQuadraticExtension.isMulCommutative_galoisGroup** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.IsQuadraticExtension`。
形式化陈述：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst_
2 : Algebra F K]   [Algebra.IsQuadraticExtension F K], IsMulCommutative Gal(K/F)
参数：F : Type u_1；K : Type u_2；K/F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsQuadraticExtension.isCyclic`：∀ (F : Type u_1) (K : Type u_2) [
inst : Field F] [inst_1 : Field K] [inst_2 : Algebra F K]   [Algebra.IsQuadratic
Extension F K], IsCyclic Ga…
-/
theorem IsQuadraticExtension.isMulCommutative_galoisGroup : IsMulCommutative Gal(K/F) :=
  inferInstance

end Algebra

