/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Applications of Maschke's theorem

This proves some properties of representations that follow from Maschke's
theorem.

We prove that, if `G` is a finite group whose order is invertible in a field `k`,
then every object of `Rep k G` (resp. `FDRep k G`) is injective and projective.

We also give two simpleness criteria for an object `V` of `FDRep k G`, when `k` is
an algebraically closed field in which the order of `G` is invertible:
* `FDRep.simple_iff_end_is_rank_one`: `V` is simple if and only `V ⟶ V` is a `k`-vector
  space of dimension `1`.
* `FDRep.simple_iff_char_is_norm_one`: when `k` is characteristic zero, `V` is simple
  if and only if `∑ g : G, V.character g * V.character g⁻¹ = Fintype.card G`.

-/

public section

universe u v w

variable {k : Type u} [Field k] {G : Type u} [Finite G] [Group G]

open CategoryTheory Limits

namespace Rep

variable [NeZero (Nat.card G : k)]

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is injective.
-/
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is injective.
-/
instance (V : Rep.{w} k G) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is projective.
-/
-- Will this clash with the previously defined `Projective` instances?
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Rep.{u} k G) : Projective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff,
    ← IsProjective.iff_projective]
  exact Module.projective_of_isSemisimpleRing _ _

end Rep

namespace FDRep

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is injective.
-/
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is injective.
-/
instance [NeZero (Nat.card G : k)] (V : FDRep k G) : Injective V :=
  (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is projective.
-/
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is projective.
-/
instance [NeZero (Nat.card G : k)] (V : FDRep k G) : Projective V :=
  (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective inferInstance

variable [IsAlgClosed k]

/--
If `G` is finite and its order is nonzero in an algebraically closed field `k`,
then an object of `FDRep k G` is simple if and only if its space of endomorphisms is
a `k`-vector space of dimension `1`.
-/
/-
**FDRep.simple_iff_end_is_rank_one** 是 Mathlib 中的一个引理，位于命名空间 `FDRep`。
形式化陈述：simple_iff_end_is_rank_one [NeZero (Nat.card G : k)] (V : FDRep k G) : Sim
ple V ↔ Module.finrank k (V ⟶ V) = 1 where mp h
参数：Nat.card G : k；V : FDRep k G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.finrank_endomorphism_simple_eq_one`：finrank_endomorphism_
simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ 
X) = 1
· 使用定理 `FDRep.instHasKernels`：∀ {k : Type u} {G : Type v} [inst : Field k] [inst
_1 : Monoid G], CategoryTheory.Limits.HasKernels (FDRep k G)
· 使用定理 `FDRep.instFiniteDimensionalHom`：∀ {k : Type u} {G : Type v} [inst : Fiel
d k] [inst_1 : Monoid G] (V W : FDRep k G), FiniteDimensional k (V ⟶ W)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finrank_pos_iff_exists_ne_zero`：Module.finrank_pos_iff_exists_ne_
zero [IsDomain R] [IsTorsionFree R M] : 0 < finrank R M ↔ exists x : M, x != 0
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
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_src`：eq_zero_of_src {X Y : C} (o
 : IsZero X) (f : X ⟶ Y) : f = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.isIsoZero_iff_source_target_isZero`：isIsoZero_iff_
source_target_isZero (X Y : C) : IsIso (0 : X ⟶ Y) ↔ IsZero X ∧ IsZero Y
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `FDRep.instInjectiveOfNeZeroCastCard`：∀ {k : Type u} [inst : Field k] {G 
: Type u} [Finite G] [inst_2 : Group G] [NeZero ↑(Nat.card G)] (V : FDRep k G), 
  CategoryTheory.Injectiv…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `G` is finite and its order is nonzero in an algebraically closed field `k`,
then an object of `FDRep k G` is simple if and only if its space of endomorphism
s is
a `k`-vector space of dimension `1`.
-/
lemma simple_iff_end_is_rank_one [NeZero (Nat.card G : k)] (V : FDRep k G) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ := ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι ≠ 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V := (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

omit [Finite G] in
/--
If `G` is finite and `k` an algebraically closed field of characteristic `0`,
then an object of `FDRep k G` is simple if and only if its character has norm `1`.
-/
/-
**FDRep.simple_iff_char_is_norm_one** 是 Mathlib 中的一个引理，位于命名空间 `FDRep`。
形式化陈述：simple_iff_char_is_norm_one [CharZero k] [Fintype G] (V : FDRep k G) : Sim
ple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G
参数：V : FDRep k G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.instNeZeroCardOfNonemptyOfFinite`：∀ {α : Type u_1} [Nonempty α] [Fin
ite α], NeZero (Nat.card α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FDRep.char_orthonormal`：char_orthonormal (V W : FDRep k G) [Simple V] [S
imple W] : (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ = if No
nempty (V ≅ …
· 使用定理 `FDRep.scalar_product_char_eq_finrank_equivariant`：scalar_product_char_eq
_finrank_equivariant (V W : FDRep k G) : (Nat.card G : k)⁻¹ * ∑ g : G, W.charact
er g * V.character g⁻¹ = Module.finran…
· 使用引理 `FDRep.simple_iff_end_is_rank_one`：simple_iff_end_is_rank_one [NeZero (Na
t.card G : k)] (V : FDRep k G) : Simple V ↔ Module.finrank k (V ⟶ V) = 1 where m
p h
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `inv_mul_cancel_of_invertible`：inv_mul_cancel_of_invertible (a : α) [Inve
rtible a] : a⁻¹ * a = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
If `G` is finite and `k` an algebraically closed field of characteristic `0`,
then an object of `FDRep k G` is simple if and only if its character has norm `1
`.
-/
lemma simple_iff_char_is_norm_one [CharZero k] [Fintype G] (V : FDRep k G) :
    Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G := by
  have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
  constructor <;> intro h
  · symm; simpa [Nonempty.intro (Iso.refl V), inv_mul_eq_one₀] using char_orthonormal V V
  · have eq := V.scalar_product_char_eq_finrank_equivariant V
    rw [h, inv_mul_cancel_of_invertible] at eq
    rw [simple_iff_end_is_rank_one, ← Nat.cast_inj (R := k), ← eq, Nat.cast_one]

end FDRep

