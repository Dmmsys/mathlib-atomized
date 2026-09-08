/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.RingTheory.Adjoin.Singleton
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Adjoining Elements to Fields

This file relates `IntermediateField.adjoin` to `Algebra.adjoin`.
-/

public section

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/-
**IntermediateField.algebra_adjoin_le_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：algebra_adjoin_le_adjoin : Algebra.adjoin F S <= (adjoin F S).toSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

namespace algebraAdjoinAdjoin

/-- `IntermediateField.adjoin` as an algebra over `Algebra.adjoin`. -/
/-
**IntermediateField.algebraAdjoinAdjoin.** 是 Mathlib 中的一个实例，位于命名空间 `Intermediate
Field.algebraAdjoinAdjoin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IntermediateField.adjoin` as an algebra over `Algebra.adjoin`.
-/
scoped instance : Algebra (Algebra.adjoin F S) (adjoin F S) :=
  (Subalgebra.inclusion <| algebra_adjoin_le_adjoin F S).toAlgebra

@[simp]
/-
**IntermediateField.algebraAdjoinAdjoin.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField.algebraAdjoinAdjoin`。
形式化陈述：coe_algebraMap (x : Algebra.adjoin F S) : (algebraMap (Algebra.adjoin F S)
 (adjoin F S) x : E) = x
参数：x : Algebra.adjoin F S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap (x : Algebra.adjoin F S) :
    (algebraMap (Algebra.adjoin F S) (adjoin F S) x : E) = x := rfl

@[simp]
/-
**IntermediateField.algebraAdjoinAdjoin.algebraMap_eq_gen_self** 是 Mathlib 中的一个定
理，位于命名空间 `IntermediateField.algebraAdjoinAdjoin`。
形式化陈述：algebraMap_eq_gen_self {x : E} : algebraMap (Algebra.adjoin F {x}) F⟮x⟯ ⟨x
, Algebra.self_mem_adjoin_singleton F x⟩ = AdjoinSimple.gen F x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
-/
theorem algebraMap_eq_gen_self {x : E} :
    algebraMap (Algebra.adjoin F {x}) F⟮x⟯ ⟨x, Algebra.self_mem_adjoin_singleton F x⟩ =
    AdjoinSimple.gen F x := rfl
/-
**IntermediateField.algebraAdjoinAdjoin.** 是 Mathlib 中的一个实例，位于命名空间 `Intermediate
Field.algebraAdjoinAdjoin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (X) [SMul X F] [SMul X E] [IsScalarTower X F E] :
    IsScalarTower X (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.isScalarTower_left (algebra_adjoin_le_adjoin F S) _
/-
**IntermediateField.algebraAdjoinAdjoin.** 是 Mathlib 中的一个实例，位于命名空间 `Intermediate
Field.algebraAdjoinAdjoin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (X) [MulAction E X] : IsScalarTower (Algebra.adjoin F S) (adjoin F S) X :=
  Subalgebra.inclusion.isScalarTower_right (algebra_adjoin_le_adjoin F S) _
/-
**IntermediateField.algebraAdjoinAdjoin.** 是 Mathlib 中的一个实例，位于命名空间 `Intermediate
Field.algebraAdjoinAdjoin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : FaithfulSMul (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.faithfulSMul (algebra_adjoin_le_adjoin F S)
/-
**IntermediateField.algebraAdjoinAdjoin.** 是 Mathlib 中的一个实例，位于命名空间 `Intermediate
Field.algebraAdjoinAdjoin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : IsFractionRing (Algebra.adjoin F S) (adjoin F S) :=
  .of_field _ _ fun ⟨_, h⟩ ↦ have ⟨x, hx, y, hy, eq⟩ := mem_adjoin_iff_div.mp h
    ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩
/-
**IntermediateField.algebraAdjoinAdjoin.** 是 Mathlib 中的一个实例，位于命名空间 `Intermediate
Field.algebraAdjoinAdjoin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : Algebra.IsAlgebraic (Algebra.adjoin F S) (adjoin F S) :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (Algebra.adjoin F S))

end algebraAdjoinAdjoin

/-
**IntermediateField.adjoin_eq_algebra_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：adjoin_eq_algebra_adjoin (inv_mem : forall x in Algebra.adjoin F S, x⁻¹ in
 Algebra.adjoin F S) : (adjoin F S).toSubalgebra = Algebra.adjoin F S
参数：inv_mem : forall x in Algebra.adjoin F S, x⁻¹ in Algebra.adjoin F S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `IntermediateField.algebra_adjoin_le_adjoin`：algebra_adjoin_le_adjoin : A
lgebra.adjoin F S <= (adjoin F S).toSubalgebra
-/
theorem adjoin_eq_algebra_adjoin (inv_mem : ∀ x ∈ Algebra.adjoin F S, x⁻¹ ∈ Algebra.adjoin F S) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymm
    (show adjoin F S ≤
        { Algebra.adjoin F S with
          inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)
/-
**IntermediateField.eq_adjoin_of_eq_algebra_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E) (h : K.toSubalg
ebra = Algebra.adjoin F S) : K = adjoin F S
参数：K : IntermediateField F E；h : K.toSubalgebra = Algebra.adjoin F S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_eq_algebra_adjoin`：adjoin_eq_algebra_adjoin (in
v_mem : forall x in Algebra.adjoin F S, x⁻¹ in Algebra.adjoin F S) : (adjoin F S
).toSubalgebra = Algebra.adjoin …
· 使用定理 `IntermediateField.inv_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → x⁻…
-/
theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E)
    (h : K.toSubalgebra = Algebra.adjoin F S) : K = adjoin F S := by
  apply toSubalgebra_injective
  rw [h]
  refine (adjoin_eq_algebra_adjoin F _ fun x ↦ ?_).symm
  rw [← h]
  exact K.inv_mem
/-
**IntermediateField.adjoin_eq_top_of_algebra** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤
参数：hS : Algebra.adjoin F S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.algebra_adjoin_le_adjoin`：algebra_adjoin_le_adjoin : A
lgebra.adjoin F S <= (adjoin F S).toSubalgebra
-/
theorem adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤ :=
  top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

section FG

variable {F}

open scoped algebraAdjoinAdjoin in
/-
**IntermediateField.fg_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateField`。
形式化陈述：fg_top_iff : (⊤ : IntermediateField F E).FG ↔ Algebra.EssFiniteType F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FiniteType.adjoin_of_finite`：adjoin_of_finite {A : Type*} [CommS
emiring A] [Algebra R A] {t : Set A} (h : Set.Finite t) : FiniteType R (Algebra.
adjoin R t)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Algebra.EssFiniteType.of_isLocalization`：∀ {R : Type u_1} (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid
 R)   [IsLocalization M S], A…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsFractionRingSubtypeMemSubalg
ebraAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fie
ld E] [inst_2 : Algebra F E] (S : Set E),   IsFractionRing ↥(Algebra.adjoin F …
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fiel
d E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : SMul X F] …
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.EssFiniteType.of_surjective`：∀ {R : Type u_1} {S : Type u_2} {T 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [i
nst_3 : Algebra R S] [ins…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Algebra.EssFiniteType.isLocalization`：∀ (R : Type u_1) (S : Type u_2) [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [h : Algebra.Es
sFiniteType R S], IsLocali…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.algebra_adjoin_le_adjoin`：algebra_adjoin_le_adjoin : A
lgebra.adjoin F S <= (adjoin F S).toSubalgebra
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma fg_top_iff :
    (⊤ : IntermediateField F E).FG ↔ Algebra.EssFiniteType F E := by
  constructor
  · intro ⟨s, hs⟩
    have : Algebra.FiniteType F (Algebra.adjoin F (s : Set E)) := .adjoin_of_finite s.finite_toSet
    have : Algebra.EssFiniteType (Algebra.adjoin F (s : Set E)) (adjoin F (s : Set E)) :=
      .of_isLocalization _ (nonZeroDivisors _)
    have : Algebra.EssFiniteType F (adjoin F (s : Set E)) :=
      .comp _ (Algebra.adjoin F (s : Set E)) _
    rw [hs] at this
    exact .of_surjective IntermediateField.topEquiv.toAlgHom IntermediateField.topEquiv.surjective
  · intro _
    use Algebra.EssFiniteType.finset F E
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.EssFiniteType.submonoid F E) x
    have hs : s.1.1 ≠ 0 := (IsLocalization.map_units E s).ne_zero
    have H : IsLocalization.mk' E x s = x / s := by
      simp [IsLocalization.mk'_eq_iff_eq_mul, hs]
    rw [H]
    exact div_mem (IntermediateField.algebra_adjoin_le_adjoin _ _ x.2)
      (IntermediateField.algebra_adjoin_le_adjoin _ _ s.1.2)

variable (F E) in
/-
**IntermediateField.fg_top** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateField`。
形式化陈述：fg_top [Algebra.EssFiniteType F E] : (⊤ : IntermediateField F E).FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IntermediateField.fg_top_iff`：fg_top_iff : (⊤ : IntermediateField F E).F
G ↔ Algebra.EssFiniteType F E
-/
lemma fg_top [Algebra.EssFiniteType F E] : (⊤ : IntermediateField F E).FG := by
  rwa [fg_top_iff]
/-
**IntermediateField.essFiniteType_iff** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：essFiniteType_iff {K : IntermediateField F E} : Algebra.EssFiniteType F K 
↔ K.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.map_injective`：map_injective (f : L ->ₐ[K] L') : Funct
ion.Injective (map f)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IntermediateField.adjoin_map`：adjoin_map {E' : Type*} [Field E'] [Algebr
a F E'] (f : E ->ₐ[F] E') : (adjoin F S).map f = adjoin F (f '' S)
· 使用定理 `IntermediateField.fieldRange_val`：fieldRange_val : S.val.fieldRange = S
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `Equiv.finsetSubtypeComm_symm_apply`：∀ {α : Type u_1} (p : α → Prop) (s :
 { s // ∀ a ∈ s, p a }),   (Equiv.finsetSubtypeComm p).symm s = Finset.map (Subt
ype.impEmbedding (Member…
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.impEmbedding_apply_coe`：∀ {α : Type u_1} (p q : α → Prop) (h : ∀
 (x : α), p x → q x) (x : { x // p x }), ↑((Subtype.impEmbedding p q h) x) = ↑x
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma essFiniteType_iff {K : IntermediateField F E} :
    Algebra.EssFiniteType F K ↔ K.FG := by
  suffices (∃ s : Finset E, (s : Set E) ⊆ K ∧ adjoin F ↑s = K) ↔
      ∃ t : Finset E, adjoin F ↑t = K by
    simpa [IntermediateField.FG, (Equiv.finsetSubtypeComm _).exists_congr_left,
      ← (IntermediateField.map_injective K.val).eq_iff, ← IntermediateField.fg_top_iff,
      adjoin_map, ← Set.range_comp, Function.comp_def, ← AlgHom.fieldRange_eq_map] using! this
  exact ⟨fun ⟨s, _, hs⟩ ↦ ⟨s, hs⟩, fun ⟨s, hs⟩ ↦ ⟨s, hs ▸ subset_adjoin _ _, hs⟩⟩

/-- A field is finitely generated if and only if it is essentially of finite type over its prime
subfield. -/
/-
**IntermediateField._root_.Field.fg_iff_essFiniteType** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field is finitely generated if and only if it is essentially of finite type ov
er its prime
subfield.
-/
theorem _root_.Field.fg_iff_essFiniteType : Field.FG F ↔ Algebra.EssFiniteType (⊥ : Subfield F) F :=
  Field.fg_iff_fg_top_bot.trans fg_top_iff

end FG

section AdjoinSimple

open Algebra

variable (α : E)

@[simp]
/-
**IntermediateField.AdjoinSimple.isIntegral_gen** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField.AdjoinSimple`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (α : E),   IsIntegral F (IntermediateField.AdjoinSimple.gen F α
) ↔ IsIntegral F α
参数：F : Type u_1；α : E；IntermediateField.AdjoinSimple.gen F α。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem AdjoinSimple.isIntegral_gen : IsIntegral F (AdjoinSimple.gen F α) ↔ IsIntegral F α := by
  conv_rhs => rw [← AdjoinSimple.algebraMap_gen F α]
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]

variable {F} {α}
/-
**IntermediateField.adjoin_toSubalgebra_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：adjoin_toSubalgebra_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlge
braic F x) : (adjoin F S).toSubalgebra = Algebra.adjoin F S
参数：hS : forall x in S, IsAlgebraic F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_eq_algebra_adjoin`：adjoin_eq_algebra_adjoin (in
v_mem : forall x in Algebra.adjoin F S, x⁻¹ in Algebra.adjoin F S) : (adjoin F S
).toSubalgebra = Algebra.adjoin …
· 使用定理 `Algebra.IsIntegral.inv_mem`：Algebra.IsIntegral.inv_mem [Algebra.IsIntegr
al R A] (hx : x in A) : x⁻¹ in A
· 使用定理 `Algebra.IsIntegral.adjoin`：Algebra.IsIntegral.adjoin {S : Set A} (hS : f
orall x in S, IsIntegral R x) : Algebra.IsIntegral R (adjoin R S)
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
-/
theorem adjoin_toSubalgebra_of_isAlgebraic {S : Set E} (hS : ∀ x ∈ S, IsAlgebraic F x) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_eq_algebra_adjoin _ _ fun _ ↦
    (Algebra.IsIntegral.adjoin fun x hx ↦ (hS x hx).isIntegral).inv_mem
/-
**IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic** 是 Mathlib 中的一个定理
，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_simple_toSubalgebra_of_isAlgebraic (hα : IsAlgebraic F α) : F⟮α⟯.to
Subalgebra = F[α]
参数：hα : IsAlgebraic F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem adjoin_simple_toSubalgebra_of_isAlgebraic (hα : IsAlgebraic F α) :
    F⟮α⟯.toSubalgebra = F[α] :=
  adjoin_toSubalgebra_of_isAlgebraic <| by simpa

@[simp]
/-
**IntermediateField.adjoin_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：adjoin_toSubalgebra [Algebra.IsAlgebraic F E] (S : Set E) : (adjoin F S).t
oSubalgebra = Algebra.adjoin F S
参数：S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem adjoin_toSubalgebra [Algebra.IsAlgebraic F E] (S : Set E) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_toSubalgebra_of_isAlgebraic fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x
/-
**IntermediateField.adjoin_eq_top_iff_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：adjoin_eq_top_iff_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebr
aic F x) : adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤
参数：hS : forall x in S, IsAlgebraic F x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `IntermediateField.toSubalgebra_inj`：toSubalgebra_inj : F.toSubalgebra = 
E.toSubalgebra ↔ F = E
· 使用定理 `IntermediateField.top_toSubalgebra`：top_toSubalgebra : (⊤ : Intermediate
Field F E).toSubalgebra = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem adjoin_eq_top_iff_of_isAlgebraic {S : Set E} (hS : ∀ x ∈ S, IsAlgebraic F x) :
    adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hS,
      ← IntermediateField.toSubalgebra_inj,
      IntermediateField.top_toSubalgebra]

alias ⟨_root_.Algebra.adjoin_eq_top_of_intermediateField, _⟩ := adjoin_eq_top_iff_of_isAlgebraic
/-
**IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic** 是 Mathlib 中的一个定理，位
于命名空间 `IntermediateField`。
形式化陈述：adjoin_simple_eq_top_iff_of_isAlgebraic {x : E} (hx : IsAlgebraic F x) : F
⟮x⟯ = ⊤ ↔ F[x] = ⊤
参数：hx : IsAlgebraic F x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_eq_top_iff_of_isAlgebraic`：adjoin_eq_top_iff_of
_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : adjoin F S = ⊤ 
↔ Algebra.adjoin F S = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem adjoin_simple_eq_top_iff_of_isAlgebraic {x : E} (hx : IsAlgebraic F x) :
    F⟮x⟯ = ⊤ ↔ F[x] = ⊤ := adjoin_eq_top_iff_of_isAlgebraic (by simp [hx])

alias ⟨_root_.Algebra.adjoin_eq_top_of_primitive_element, _⟩ :=
  adjoin_simple_eq_top_iff_of_isAlgebraic

@[simp]
/-
**IntermediateField.adjoin_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：adjoin_eq_top_iff [Algebra.IsAlgebraic F E] {S : Set E} : adjoin F S = ⊤ ↔
 Algebra.adjoin F S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_eq_top_iff_of_isAlgebraic`：adjoin_eq_top_iff_of
_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : adjoin F S = ⊤ 
↔ Algebra.adjoin F S = ⊤
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem adjoin_eq_top_iff [Algebra.IsAlgebraic F E] {S : Set E} :
    adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤ :=
  adjoin_eq_top_iff_of_isAlgebraic (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)
/-
**IntermediateField._root_.Algebra.finite_of_essFiniteType_of_isAlgebraic** 是 Ma
thlib 中的一个引理，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.finite_of_essFiniteType_of_isAlgebraic
    [Algebra.EssFiniteType F E] [Algebra.IsAlgebraic F E] :
    Module.Finite F E := by
  obtain ⟨s, hs⟩ := fg_top F E
  have : Algebra.FiniteType F E := by
    use s
    rw [← adjoin_toSubalgebra_of_isAlgebraic fun x hx ↦ Algebra.IsAlgebraic.isAlgebraic x]
    simpa [← toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

section RingHom

variable {A B C : Type*} [Field A] [CommSemiring B] [Field C] [Algebra A B]
  [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

/-- Ring homomorphism between `A[b]` and `A⟮↑b⟯`. -/
/-
**IntermediateField.RingHom.adjoinAlgebraMapOfAlgebra** 是 Mathlib 中的一个定义，位于命名空间 
`IntermediateField.RingHom`。
形式化陈述：{A : Type u_3} →   {B : Type u_4} →     {C : Type u_5} →       [inst : Fie
ld A] →         [inst_1 : CommSemiring B] →           [inst_2 : Field C] →      
       [inst_3 : Algebra A B] →               [inst_4 : Algebra B C] →          
       [inst_5 : Algebra A C] → [IsScalarTower A B C] → (b : B) → ↥A[b] →+* ↥A⟮(
algebraMap B C) b⟯
参数：b : B；algebraMap B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphism between `A[b]` and `A⟮↑b⟯`.
-/
noncomputable def RingHom.adjoinAlgebraMapOfAlgebra :
    A[b] →+* A⟮((algebraMap B C) b)⟯ :=
  RingHom.comp (Subalgebra.inclusion <|
    algebra_adjoin_le_adjoin A {((algebraMap B C) b)}).toRingHom
    (Algebra.RingHom.adjoinAlgebraMap b)
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra (A[b]) A⟮(algebraMap B C) b⟯ :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMapOfAlgebra _)
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower (A[b]) A⟮(algebraMap B C) b⟯ C :=
  IsScalarTower.of_algebraMap_eq' rfl

end RingHom

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

/-
**IntermediateField.le_sup_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra <= (E1 ⊔ E2).toSub
algebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra ≤ (E1 ⊔ E2).toSubalgebra :=
  sup_le (show E1 ≤ E1 ⊔ E2 from le_sup_left) (show E2 ≤ E1 ⊔ E2 from le_sup_right)
/-
**IntermediateField.sup_toSubalgebra_of_isAlgebraic_right** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField`。
形式化陈述：sup_toSubalgebra_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E
2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `IsAlgebraic.tower_top`：IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebrai
c K x) : IsAlgebraic L x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.isAlgebraic_iff`：isAlgebraic_iff {x : S} : IsAlgebraic
 K x ↔ IsAlgebraic K (x : L)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.restrictScalars_adjoin`：Algebra.restrictScalars_adjoin (F : Type
*) [CommSemiring F] {E : Type*} [CommSemiring E] [Algebra F E] (K : Subalgebra F
 E) (S : Set E) : (A…
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.restrictScalars_toSubalgebra`：restrictScalars_toSubalg
ebra {E : IntermediateField L' L} : (E.restrictScalars K).toSubalgebra = E.toSub
algebra.restrictScalars K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem sup_toSubalgebra_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have : (adjoin E1 (E2 : Set L)).toSubalgebra = _ := adjoin_toSubalgebra_of_isAlgebraic fun x h ↦
    IsAlgebraic.tower_top _ (isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (⟨x, h⟩ : E2)))
  apply_fun Subalgebra.restrictScalars K at this
  rw [← restrictScalars_toSubalgebra, restrictScalars_adjoin] at this
  -- TODO: rather than using `← coe_type_toSubalgebra` here, perhaps we should restate another
  -- version of `Algebra.restrictScalars_adjoin` for intermediate fields?
  simp only [← coe_type_toSubalgebra] at this
  rw [Algebra.restrictScalars_adjoin] at this
  exact this
/-
**IntermediateField.sup_toSubalgebra_of_isAlgebraic_left** 是 Mathlib 中的一个定理，位于命名
空间 `IntermediateField`。
形式化陈述：sup_toSubalgebra_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] : (E1 ⊔ E2
).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`：sup_toSubalgebr
a_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E2).toSubalgebra = E1.
toSubalgebra ⊔ E2.toSubalgebra
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sup_toSubalgebra_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have := sup_toSubalgebra_of_isAlgebraic_right E2 E1
  rwa [sup_comm (a := E1), sup_comm (a := E1.toSubalgebra)]

/-- The compositum of two intermediate fields is equal to the compositum of them
as subalgebras, if one of them is algebraic over the base field. -/
/-
**IntermediateField.sup_toSubalgebra_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：sup_toSubalgebra_of_isAlgebraic (halg : Algebra.IsAlgebraic K E1 ∨ Algebra
.IsAlgebraic K E2) : (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra
参数：halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_left`：sup_toSubalgebra
_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] : (E1 ⊔ E2).toSubalgebra = E1.to
Subalgebra ⊔ E2.toSubalgebra
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`：sup_toSubalgebr
a_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E2).toSubalgebra = E1.
toSubalgebra ⊔ E2.toSubalgebra

--- 原说明 ---
The compositum of two intermediate fields is equal to the compositum of them
as subalgebras, if one of them is algebraic over the base field.
-/
theorem sup_toSubalgebra_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  halg.elim (fun _ ↦ sup_toSubalgebra_of_isAlgebraic_left E1 E2)
    (fun _ ↦ sup_toSubalgebra_of_isAlgebraic_right E1 E2)
/-
**IntermediateField.sup_toSubalgebra_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：sup_toSubalgebra_of_left [FiniteDimensional K E1] : (E1 ⊔ E2).toSubalgebra
 = E1.toSubalgebra ⊔ E2.toSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_left`：sup_toSubalgebra
_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] : (E1 ⊔ E2).toSubalgebra = E1.to
Subalgebra ⊔ E2.toSubalgebra
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem sup_toSubalgebra_of_left [FiniteDimensional K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_left E1 E2
/-
**IntermediateField.sup_toSubalgebra_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：sup_toSubalgebra_of_right [FiniteDimensional K E2] : (E1 ⊔ E2).toSubalgebr
a = E1.toSubalgebra ⊔ E2.toSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`：sup_toSubalgebr
a_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E2).toSubalgebra = E1.
toSubalgebra ⊔ E2.toSubalgebra
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem sup_toSubalgebra_of_right [FiniteDimensional K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_right E1 E2

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / F`, such that
either `E / F` or `L / F` is algebraic, then `E(L) = E[L]`. -/
/-
**IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic** 是 Mat
hlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateFiel
d F K) (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) : (adjoin E (L
 : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K)
参数：L : IntermediateField F K；halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebrai
c F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subalgebra.restrictScalars_injective`：restrictScalars_injective : Functi
on.Injective (restrictScalars R : Subalgebra S A -> Subalgebra R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.restrictScalars_toSubalgebra`：restrictScalars_toSubalg
ebra {E : IntermediateField L' L} : (E.restrictScalars K).toSubalgebra = E.toSub
algebra.restrictScalars K
· 使用定理 `IntermediateField.restrictScalars_adjoin_of_algEquiv`：restrictScalars_ad
join_of_algEquiv {L L' : Type*} [Field L] [Field L'] [Algebra F L] [Algebra L E]
 [Algebra F L'] [Algebra L' E] [IsScalarTo…
· 使用定理 `Algebra.restrictScalars_adjoin_of_algEquiv`：Algebra.restrictScalars_adjo
in_of_algEquiv {F E L L' : Type*} [CommSemiring F] [CommSemiring L] [CommSemirin
g L'] [Semiring E] [Algebra F L]…
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.restrictScalars_adjoin`：Algebra.restrictScalars_adjoin (F : Type
*) [CommSemiring F] {E : Type*} [CommSemiring E] [Algebra F E] (K : Subalgebra F
 E) (S : Set E) : (A…
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic`：sup_toSubalgebra_of_i
sAlgebraic (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) : (E1 ⊔ 
E2).toSubalgebra = E1.toSubalgebra ⊔ E2…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B

--- 原说明 ---
If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / 
F`, such that
either `E / F` or `L / F` is algebraic, then `E(L) = E[L]`.
-/
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) := by
  let i := IsScalarTower.toAlgHom F E K
  let E' := i.fieldRange
  let i' : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField i
  have hi : algebraMap E K = (algebraMap E' K) ∘ i' := by ext x; rfl
  apply_fun _ using Subalgebra.restrictScalars_injective F
  rw [← restrictScalars_toSubalgebra, restrictScalars_adjoin_of_algEquiv i' hi,
    Algebra.restrictScalars_adjoin_of_algEquiv i' hi, restrictScalars_adjoin]
  dsimp only [← E'.coe_type_toSubalgebra]
  rw [Algebra.restrictScalars_adjoin F E'.toSubalgebra]
  exact E'.sup_toSubalgebra_of_isAlgebraic L (halg.imp
    (fun (_ : Algebra.IsAlgebraic F E) ↦ i'.isAlgebraic) id)
/-
**IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left** 
是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left (L : Intermediat
eField F K) [halg : Algebra.IsAlgebraic F E] : (adjoin E (L : Set K)).toSubalgeb
ra = Algebra.adjoin E (L : Set K)
参数：L : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic`：
adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
 (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) …
-/
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inl halg)
/-
**IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right**
 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right (L : Intermedia
teField F K) [halg : Algebra.IsAlgebraic F L] : (adjoin E (L : Set K)).toSubalge
bra = Algebra.adjoin E (L : Set K)
参数：L : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic`：
adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
 (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) …
-/
theorem adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_intermediateField_toSubalgebra_of_isAlgebraic E L (Or.inr halg)

end Tower

end AdjoinSimple

end AdjoinDef

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-
**IntermediateField.fg_of_fg_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：fg_of_fg_toSubalgebra (S : IntermediateField F E) (h : S.toSubalgebra.FG) 
: S.FG
参数：S : IntermediateField F E；h : S.toSubalgebra.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.eq_adjoin_of_eq_algebra_adjoin`：eq_adjoin_of_eq_algebr
a_adjoin (K : IntermediateField F E) (h : K.toSubalgebra = Algebra.adjoin F S) :
 K = adjoin F S
-/
theorem fg_of_fg_toSubalgebra (S : IntermediateField F E) (h : S.toSubalgebra.FG) : S.FG := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩
/-
**IntermediateField.fg_of_noetherian** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.FG
参数：S : IntermediateField F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.fg_of_fg_toSubalgebra`：fg_of_fg_toSubalgebra (S : Inte
rmediateField F E) (h : S.toSubalgebra.FG) : S.FG
· 使用定理 `Subalgebra.fg_of_noetherian`：fg_of_noetherian [IsNoetherian R A] (S : Su
balgebra R A) : S.FG
-/
theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.FG :=
  S.fg_of_fg_toSubalgebra S.toSubalgebra.fg_of_noetherian
/-
**IntermediateField.induction_on_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：induction_on_adjoin [FiniteDimensional F E] (P : IntermediateField F E -> 
Prop) (base : P ⊥) (ih : forall (K : IntermediateField F E) (x : E), P K -> P (K
⟮x⟯.restrictScalars F)) (K : IntermediateField F E) : P K
参数：P : IntermediateField F E -> Prop；base : P ⊥；ih : forall (K : IntermediateFie
ld F E) (x : E), P K -> P (K⟮x⟯.restrictScalars F)；K : IntermediateField F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.induction_on_adjoin_fg`：induction_on_adjoin_fg (P : In
termediateField F E -> Prop) (base : P ⊥) (ih : forall (K : IntermediateField F 
E) (x : E), P K -> P (K⟮x⟯.res…
· 使用定理 `IntermediateField.fg_of_noetherian`：fg_of_noetherian (S : IntermediateFi
eld F E) [IsNoetherian F E] : S.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsNoetherian.iff_fg`：iff_fg : IsNoetherian K V ↔ Module.Finite K V
-/
theorem induction_on_adjoin [FiniteDimensional F E] (P : IntermediateField F E → Prop)
    (base : P ⊥) (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) : P K :=
  letI : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end Induction

end IntermediateField

namespace IsFractionRing

variable {F A K L : Type*} [Field F] [CommRing A] [Algebra F A]
  [Field K] [Algebra F K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra F L]
  {g : A →ₐ[F] L} {f : K →ₐ[F] L}

/-- If `F` is a field, `A` is an `F`-algebra with fraction field `K`, `L` is a field,
`g : A →ₐ[F] L` lifts to `f : K →ₐ[F] L`,
then the image of `f` is the field generated by the image of `g`.
Note: this does not require `IsScalarTower F A K`. -/
/-
**IsFractionRing.algHom_fieldRange_eq_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsFr
actionRing`。
形式化陈述：algHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = (g 
: A ->+* L)) : f.fieldRange = IntermediateField.adjoin F g.range
参数：h : RingHom.comp f (algebraMap A K) = (g : A ->+* L)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IntermediateField.toSubfield_injective`：toSubfield_injective : Function.
Injective (toSubfield : IntermediateField K L -> _)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsFractionRing.ringHom_fieldRange_eq_of_comp_eq`：ringHom_fieldRange_eq_o
f_comp_eq (h : RingHom.comp f (algebraMap A K) = g) : f.fieldRange = Subfield.cl
osure g.range

--- 原说明 ---
If `F` is a field, `A` is an `F`-algebra with fraction field `K`, `L` is a field
,
`g : A →ₐ[F] L` lifts to `f : K →ₐ[F] L`,
then the image of `f` is the field generated by the image of `g`.
Note: this does not require `IsScalarTower F A K`.
-/
theorem algHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = (g : A →+* L)) :
    f.fieldRange = IntermediateField.adjoin F g.range := by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  convert! ringHom_fieldRange_eq_of_comp_eq h using 2
  exact Set.union_eq_self_of_subset_left fun _ ⟨x, hx⟩ ↦ ⟨algebraMap F A x, by simp [← hx]⟩

/-- If `F` is a field, `A` is an `F`-algebra with fraction field `K`, `L` is a field,
`g : A →ₐ[F] L` lifts to `f : K →ₐ[F] L`,
`s` is a set such that the image of `g` is the subalgebra generated by `s`,
then the image of `f` is the intermediate field generated by `s`.
Note: this does not require `IsScalarTower F A K`. -/
/-
**IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq** 是 Mathlib 中的一个定理，
位于命名空间 `IsFractionRing`。
形式化陈述：algHom_fieldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMa
p A K) = (g : A ->+* L)) {s : Set L} (hs : g.range = Algebra.adjoin F s) : f.fie
ldRange = IntermediateField.adjoin F s
参数：h : RingHom.comp f (algebraMap A K) = (g : A ->+* L)；hs : g.range = Algebra.a
djoin F s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IntermediateField.toSubfield_injective`：toSubfield_injective : Function.
Injective (toSubfield : IntermediateField K L -> _)
· 使用定理 `IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq`：ringHom_fie
ldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = g) {s :
 Set L} (hs : g.range = Subring.closure s) : f.fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_eq_ring_closure`：adjoin_eq_ring_closure (s : Set A) : (ad
join R s).toSubring = Subring.closure (Set.range (algebraMap R A) union s)

--- 原说明 ---
If `F` is a field, `A` is an `F`-algebra with fraction field `K`, `L` is a field
,
`g : A →ₐ[F] L` lifts to `f : K →ₐ[F] L`,
`s` is a set such that the image of `g` is the subalgebra generated by `s`,
then the image of `f` is the intermediate field generated by `s`.
Note: this does not require `IsScalarTower F A K`.
-/
theorem algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (h : RingHom.comp f (algebraMap A K) = (g : A →+* L))
    {s : Set L} (hs : g.range = Algebra.adjoin F s) :
    f.fieldRange = IntermediateField.adjoin F s := by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  refine ringHom_fieldRange_eq_of_comp_eq_of_range_eq h ?_
  rw [← Algebra.adjoin_eq_ring_closure, ← hs]; rfl

variable [IsScalarTower F A K]

/-- The image of `IsFractionRing.liftAlgHom` is the intermediate field generated by the image
of the algebra hom. -/
/-
**IsFractionRing.liftAlgHom_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing
`。
形式化陈述：liftAlgHom_fieldRange (hg : Function.Injective g) : (liftAlgHom hg : K ->ₐ
[F] L).fieldRange = IntermediateField.adjoin F g.range
参数：hg : Function.Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.algHom_fieldRange_eq_of_comp_eq`：algHom_fieldRange_eq_of_
comp_eq (h : RingHom.comp f (algebraMap A K) = (g : A ->+* L)) : f.fieldRange = 
IntermediateField.adjoin F g.range
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `IsFractionRing.liftAlgHom` is the intermediate field generated by 
the image
of the algebra hom.
-/
theorem liftAlgHom_fieldRange (hg : Function.Injective g) :
    (liftAlgHom hg : K →ₐ[F] L).fieldRange = IntermediateField.adjoin F g.range :=
  algHom_fieldRange_eq_of_comp_eq (by ext; simp)

/-- The image of `IsFractionRing.liftAlgHom` is the intermediate field generated by `s`,
if the image of the algebra hom is the subalgebra generated by `s`. -/
/-
**IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 
`IsFractionRing`。
形式化陈述：liftAlgHom_fieldRange_eq_of_range_eq (hg : Function.Injective g) {s : Set 
L} (hs : g.range = Algebra.adjoin F s) : (liftAlgHom hg : K ->ₐ[F] L).fieldRange
 = IntermediateField.adjoin F s
参数：hg : Function.Injective g；hs : g.range = Algebra.adjoin F s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq`：algHom_field
Range_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = (g : A ->
+* L)) {s : Set L} (hs : g.range = Algebra.adjoi…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `IsFractionRing.liftAlgHom` is the intermediate field generated by 
`s`,
if the image of the algebra hom is the subalgebra generated by `s`.
-/
theorem liftAlgHom_fieldRange_eq_of_range_eq (hg : Function.Injective g)
    {s : Set L} (hs : g.range = Algebra.adjoin F s) :
    (liftAlgHom hg : K →ₐ[F] L).fieldRange = IntermediateField.adjoin F s :=
  algHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

end IsFractionRing

