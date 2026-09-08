/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.DepRewrite

/-!
# Ideal sheaves on schemes

We define ideal sheaves of schemes and provide various constructors for it.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData`: A structure that contains the data to uniquely define
  an ideal sheaf, consisting of
  1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
  2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`:
  The largest ideal sheaf contained in a family of ideals.
* `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`:
  Over affine schemes, ideal sheaves are in bijection with ideals of the global sections.
* `AlgebraicGeometry.Scheme.IdealSheafData.support`: The support of an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`: The vanishing ideal of a set.
* `AlgebraicGeometry.Scheme.Hom.ker`: The kernel of a morphism.

## Main results
* `AlgebraicGeometry.Scheme.IdealSheafData.gc`:
  `support` and `vanishingIdeal` forms a Galois connection.
* `AlgebraicGeometry.Scheme.Hom.support_ker`: The support of a kernel of a quasi-compact morphism
  is the closure of the range.

## Implementation detail

Ideal sheaves are not yet defined in this file as actual subsheaves of `𝒪ₓ`.
Instead, for the ease of development and application,
we define the structure `IdealSheafData` containing all necessary data to uniquely define an
ideal sheaf. This should be refactored as a constructor for ideal sheaves once they are introduced
into mathlib.

-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/--
A structure that contains the data to uniquely define an ideal sheaf, consisting of
1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`
3. a subset of `X` equal to the support.

Also see `Scheme.IdealSheafData.mkOfMemSupportIff` for a constructor with the condition on the
support being (usually) easier to prove.
-/
/-
**AlgebraicGeometry.Scheme.IdealSheafData** 是 Mathlib 中的一个结构，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：IdealSheafData (X : Scheme.{u}) : Type u where /-- The component of an ide
al sheaf at an affine open. -/ ideal : forall U : X.affineOpens, Ideal Γ(X, U) /
-- Also see `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` -/ map_ideal_bas
icOpen : forall (U : X.affineOpens) (f : Γ(X, U)), (ideal U).map (X.presheaf.map
 (homOfLE <| X.basicOpen_le f).op).hom = ideal (X.affineBasicOpen f) /-- The sup
port of an ideal sheaf. Use `IdealSheafData.support` instead for most occasions.
 -/ supportSet : Set X
参数：X : Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure that contains the data to uniquely define an ideal sheaf, consisting
 of
1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `
f : Γ(X, U)`
3. a subset of `X` equal to the support.

Also see `Scheme.IdealSheafData.mkOfMemSupportIff` for a constructor with the co
ndition on the
support being (usually) easier to prove.
-/
structure IdealSheafData (X : Scheme.{u}) : Type u where
  /-- The component of an ideal sheaf at an affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal Γ(X, U)
  /-- Also see `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` -/
  map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
    (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
      ideal (X.affineBasicOpen f)
  /-- The support of an ideal sheaf. Use `IdealSheafData.support` instead for most occasions. -/
  supportSet : Set X := ⋂ U, X.zeroLocus (U := U.1) (ideal U)
  supportSet_eq_iInter_zeroLocus : supportSet = ⋂ U, X.zeroLocus (U := U.1) (ideal U) := by rfl

namespace IdealSheafData

@[ext]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {I J : X.IdealSheafData}, I.ideal = J.ide
al → I = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected lemma ext {I J : X.IdealSheafData} (h : I.ideal = J.ideal) : I = J := by
  obtain ⟨i, _, s, hs⟩ := I
  obtain ⟨j, _, t, ht⟩ := J
  subst h
  congr
  rw [hs, ht]

section Order

/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (IdealSheafData X) := PartialOrder.lift ideal fun _ _ ↦ IdealSheafData.ext
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_def** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_def {I J : IdealSheafData X} : I <= J ↔ forall U, I.ideal U <= J.ideal 
U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def {I J : IdealSheafData X} : I ≤ J ↔ ∀ U, I.ideal U ≤ J.ideal U := .rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeSup (IdealSheafData X) where
  sSup s :=
  { ideal := sSup (ideal '' s),
    map_ideal_basicOpen := by
      have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
        conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
        rfl
      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
  isLUB_sSup _ := .of_image (f := ideal) le_def (isLUB_sSup _)

/-- The largest ideal sheaf contained in a family of ideals. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ofIdeals (I : forall U : X.affineOpens, Ideal Γ(X, U)) : IdealSheafData X
参数：I : forall U : X.affineOpens, Ideal Γ(X, U)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest ideal sheaf contained in a family of ideals.
-/
def ofIdeals (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) : IdealSheafData X :=
  sSup { J : IdealSheafData X | J.ideal ≤ I }
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_ofIdeals_le (I : forall U : X.affineOpens, Ideal Γ(X, U)) : (ofIdeal
s I).ideal <= I
参数：I : forall U : X.affineOpens, Ideal Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
lemma ideal_ofIdeals_le (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) :
    (ofIdeals I).ideal ≤ I :=
  sSup_le (Set.forall_mem_image.mpr fun _ ↦ id)

/-- The Galois coinsertion between ideal sheaves and arbitrary families of ideals. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.gci** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.IdealSheafData`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   GaloisCoinsertion AlgebraicGeometry.Sch
eme.IdealSheafData.ideal AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois coinsertion between ideal sheaves and arbitrary families of ideals.
-/
protected def gci : GaloisCoinsertion ideal (ofIdeals (X := X)) where
  choice I hI :=
  { ideal := I
    map_ideal_basicOpen U f :=
      (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f }
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ ↦ id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))
/-
**AlgebraicGeometry.Scheme.IdealSheafData.strictMono_ideal** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：strictMono_ideal : StrictMono (ideal (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.strictMono_l`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion 
l u), StrictMono l
-/
lemma strictMono_ideal : StrictMono (ideal (X := X)) := IdealSheafData.gci.strictMono_l
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_mono** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_mono : Monotone (ideal (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.strictMono_ideal`：strictMono_ide
al : StrictMono (ideal (X
-/
lemma ideal_mono : Monotone (ideal (X := X)) := strictMono_ideal.monotone
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals_mono** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ofIdeals_mono : Monotone (ofIdeals (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
lemma ofIdeals_mono : Monotone (ofIdeals (X := X)) := IdealSheafData.gci.gc.monotone_u
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals_ideal** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ofIdeals_ideal (I : IdealSheafData X) : ofIdeals I.ideal = I
参数：I : IdealSheafData X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
lemma ofIdeals_ideal (I : IdealSheafData X) : ofIdeals I.ideal = I := IdealSheafData.gci.u_l_eq _
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_ofIdeals_iff {I : IdealSheafData X} {J} : I <= ofIdeals J ↔ I.ideal <= 
J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `GaloisCoinsertion.gc`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisCoinsertion l u), Ga
loisConnec…
-/
lemma le_ofIdeals_iff {I : IdealSheafData X} {J} : I ≤ ofIdeals J ↔ I.ideal ≤ J :=
  IdealSheafData.gci.gc.le_iff_le.symm

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (IdealSheafData X) where
  top.ideal := ⊤
  top.map_ideal_basicOpen := by simp [Ideal.map_top]
  top.supportSet := ⊥
  top.supportSet_eq_iInter_zeroLocus := by
    ext x
    simpa using X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  le_top I U := le_top

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (IdealSheafData X) where
  bot.ideal := ⊥
  bot.map_ideal_basicOpen := by simp
  bot.supportSet := ⊤
  bot.supportSet_eq_iInter_zeroLocus := by ext; simp
  bot_le I U := bot_le

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (IdealSheafData X) where
  inf I J :=
  { ideal := I.ideal ⊓ J.ideal
    map_ideal_basicOpen U f := by
      dsimp
      have : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap _ _ := rfl
      have inst := U.2.isLocalization_basicOpen f
      rw [← I.map_ideal_basicOpen U f, ← J.map_ideal_basicOpen U f, this]
      ext x
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
      simp only [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff, Ideal.mem_inf,
        exists_exists_eq_and]
      refine ⟨fun ⟨n, h₁, h₂⟩ ↦ ⟨⟨n, h₁⟩, ⟨n, h₂⟩⟩, ?_⟩
      rintro ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
      refine ⟨n₁ + n₂, ?_, ?_⟩
      · rw [add_comm, pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₁
      · rw [pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₂ }
  inf_le_left I J U := inf_le_left
  inf_le_right I J U := inf_le_right
  le_inf I J K hIJ hIK U := le_inf (hIJ U) (hIK U)
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (IdealSheafData X) where
  __ := (inferInstance : OrderTop (IdealSheafData X))
  __ := (inferInstance : OrderBot (IdealSheafData X))
  __ := (inferInstance : SemilatticeInf (IdealSheafData X))
  __ := (inferInstance : CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_top** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_top : ideal (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_top : ideal (X := X) ⊤ = ⊤ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_bot** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_bot : ideal (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_bot : ideal (X := X) ⊥ = ⊥ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_sup** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_sup {I J : IdealSheafData X} : (I ⊔ J).ideal = I.ideal ⊔ J.ideal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_sup {I J : IdealSheafData X} : (I ⊔ J).ideal = I.ideal ⊔ J.ideal := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_sSup** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_sSup {I : Set (IdealSheafData X)} : (sSup I).ideal = sSup (ideal '' 
I)
参数：IdealSheafData X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_sSup {I : Set (IdealSheafData X)} : (sSup I).ideal = sSup (ideal '' I) := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_iSup** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_iSup {ι : Type*} {I : ι -> IdealSheafData X} : (iSup I).ideal = ⨆ i,
 (I i).ideal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_sSup`：ideal_sSup {I : Set 
(IdealSheafData X)} : (sSup I).ideal = sSup (ideal '' I)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma ideal_iSup {ι : Type*} {I : ι → IdealSheafData X} : (iSup I).ideal = ⨆ i, (I i).ideal := by
  rw [← sSup_range, ← sSup_range, ideal_sSup, ← Set.range_comp, Function.comp_def]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_inf** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_inf {I J : IdealSheafData X} : (I ⊓ J).ideal = I.ideal ⊓ J.ideal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_inf {I J : IdealSheafData X} : (I ⊓ J).ideal = I.ideal ⊓ J.ideal := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_biInf** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_biInf {ι : Type*} (I : ι -> IdealSheafData X) {s : Set ι} (hs : s.Fi
nite) : (⨅ i in s, I i).ideal = ⨅ i in s, (I i).ideal
参数：I : ι -> IdealSheafData X；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iInf_insert`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{f : β → α} {s : Set β} {b : β},   ⨅ x ∈ insert b s, f x = f b ⊓ ⨅ x ∈ s, f x
-/
lemma ideal_biInf {ι : Type*} (I : ι → IdealSheafData X) {s : Set ι} (hs : s.Finite) :
    (⨅ i ∈ s, I i).ideal = ⨅ i ∈ s, (I i).ideal := by
  refine hs.induction_on _ (by simp) fun {i s} his hs e ↦ ?_
  simp only [iInf_insert, e, ideal_inf]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_iInf** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_iInf {ι : Type*} (I : ι -> IdealSheafData X) [Finite ι] : (⨅ i, I i)
.ideal = ⨅ i, (I i).ideal
参数：I : ι -> IdealSheafData X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_biInf`：ideal_biInf {ι : Ty
pe*} (I : ι -> IdealSheafData X) {s : Set ι} (hs : s.Finite) : (⨅ i in s, I i).i
deal = ⨅ i in s, (I i).ideal
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma ideal_iInf {ι : Type*} (I : ι → IdealSheafData X) [Finite ι] :
    (⨅ i, I i).ideal = ⨅ i, (I i).ideal := by
  simpa using ideal_biInf I Set.finite_univ

end Order

variable (I : IdealSheafData X)

section map_ideal

/-- subsumed by `IdealSheafData.map_ideal` below. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen_of_eq** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
subsumed by `IdealSheafData.map_ideal` below.
-/
private lemma map_ideal_basicOpen_of_eq
    {U V : X.affineOpens} (f : Γ(X, U)) (hV : V = X.affineBasicOpen f) :
    (I.ideal U).map (X.presheaf.map
        (homOfLE (X := X.Opens) (hV.trans_le (X.affineBasicOpen_le f))).op).hom =
      I.ideal V := by
  subst hV; exact I.map_ideal_basicOpen _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_ideal** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_ideal {U V : X.affineOpens} (h : U <= V) : (I.ideal V).map (X.presheaf
.map (homOfLE h).op).hom = I.ideal U
参数：h : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsAffineOpen.ideal_ext_iff`：ideal_ext_iff {I J : Ideal
 Γ(X, U)} : I = J ↔ forall (x : X) (h : x in U), I.map (X.presheaf.germ U x h).h
om = J.map (X.presheaf.germ U x h)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.exists_basicOpen_le_affine_inter`：∀ {X : AlgebraicGeom
etry.Scheme} {U : X.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ {V : X.Op
ens},       AlgebraicGeometry.IsAffineOp…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.affineBasicOpen_le`：∀ (X : AlgebraicGeometry.Sc
heme) {V : ↑X.affineOpens} (f : ↑(X.presheaf.obj (Opposite.op ↑V))), X.affineBas
icOpen f ≤ V
· 使用定理 `_private.Mathlib.AlgebraicGeometry.IdealSheaf.Basic.0.AlgebraicGeometry.
Scheme.IdealSheafData.map_ideal_basicOpen_of_eq`：∀ {X : AlgebraicGeometry.Scheme
} (I : X.IdealSheafData) {U V : ↑X.affineOpens} (f : ↑(X.presheaf.obj (Opposite.
op ↑U)))   (hV : V = X.affine…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen`：∀ {X : Alge
braicGeometry.Scheme} (self : X.IdealSheafData) (U : ↑X.affineOpens)   (f : ↑(X.
presheaf.obj (Opposite.op ↑U))),   Ideal.map (Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ideal {U V : X.affineOpens} (h : U ≤ V) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = I.ideal U := by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, h hxU⟩
  have := I.map_ideal_basicOpen_of_eq (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
  rw [← I.map_ideal_basicOpen] at this
  apply_fun Ideal.map (X.presheaf.germ (X.basicOpen g) x (hfg ▸ hxf)).hom at this
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, affineBasicOpen_coe, X.presheaf.germ_res]
    at this ⊢
  simp only [homOfLE_leOfHom, TopCat.Presheaf.germ_res', this]

/-- A form of `map_ideal` that is easier to rewrite with. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.map_ideal'** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：map_ideal' {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) : (I.idea
l V).map (X.presheaf.map h).hom = I.ideal U
参数：h : Opposite.op V.1 ⟶ .op U.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`：map_ideal {U V : X.af
fineOpens} (h : U <= V) : (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = 
I.ideal U

--- 原说明 ---
A form of `map_ideal` that is easier to rewrite with.
-/
lemma map_ideal' {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) :
    (I.ideal V).map (X.presheaf.map h).hom = I.ideal U :=
  map_ideal _ _
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_comap_ideal** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ideal_le_comap_ideal {U V : X.affineOpens} (h : U <= V) : I.ideal V <= (I.
ideal U).comap (X.presheaf.map (homOfLE h).op).hom
参数：h : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`：map_ideal {U V : X.af
fineOpens} (h : U <= V) : (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = 
I.ideal U
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma ideal_le_comap_ideal {U V : X.affineOpens} (h : U ≤ V) :
    I.ideal V ≤ (I.ideal U).comap (X.presheaf.map (homOfLE h).op).hom := by
  rw [← Ideal.map_le_iff_le_comap, ← I.map_ideal h]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_of_iSup_eq_top** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*} (U : ι -> X.affineO
pens) (hU : ⨆ i, (U i).1 = ⊤) (H : forall i, I.ideal (U i) <= J.ideal (U i)) : I
 <= J
参数：U : ι -> X.affineOpens；hU : ⨆ i, (U i).1 = ⊤；H : forall i, I.ideal (U i) <= J
.ideal (U i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `AlgebraicGeometry.exists_basicOpen_le_affine_inter`：∀ {X : AlgebraicGeom
etry.Scheme} {U : X.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ {V : X.Op
ens},       AlgebraicGeometry.IsAffineOp…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`：self_le_iSup_
basicOpen_iff {s : Set Γ(X, U)} : (U <= ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s
 = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Submodule.le_of_isLocalized_span`：Submodule.le_of_isLocalized_span {N P 
: Submodule R M} (h : forall r : s, N.localized₀ (.powers r.1) (f r) <= P.locali
zed₀ (.powers r.1) (f …
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Submodule.restrictScalars_localized'`：restrictScalars_localized' : (loca
lized' S p f M').restrictScalars R = localized₀ p f M'
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Ideal.localized'_eq_map`：∀ {R : Type u_1} (S : Type u_2) [inst : CommSem
iring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   (p : Submonoid R) [i
nst_3 : IsLoc…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`：map_ideal {U V : X.af
fineOpens} (h : U <= V) : (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = 
I.ideal U
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma le_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (H : ∀ i, I.ideal (U i) ≤ J.ideal (U i)) :
    I ≤ J := by
  intro V
  have : ∀ x : V.1, ∃ (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 ∈ X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter V.2 (U i).2 _ ⟨hxV, hi⟩⟩
  choose i r rU e hxr using this
  have : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.le_of_isLocalized_span _ this (fun i ↦ Γ(X, X.basicOpen i.1))
    (fun i ↦ Algebra.linearMap Γ(X, V.1) Γ(X, X.basicOpen i.1)) ?_
  rintro ⟨_, j, rfl⟩
  simp only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (r j)),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  erw [I.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j)),
    J.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j))]
  delta algebra_section_section_basicOpen
  rw! [e]
  rw [← I.map_ideal (V := (U _)) (X.basicOpen_le _), ← J.map_ideal (V := (U _)) (X.basicOpen_le _)]
  exact Ideal.map_mono (f := (X.presheaf.map (homOfLE (X.basicOpen_le (rU j))).op).hom) (H (i j))
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ext_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*} (U : ι -> X.affine
Opens) (hU : ⨆ i, (U i).1 = ⊤) (H : forall i, I.ideal (U i) = J.ideal (U i)) : I
 = J
参数：U : ι -> X.affineOpens；hU : ⨆ i, (U i).1 = ⊤；H : forall i, I.ideal (U i) = J.
ideal (U i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_of_iSup_eq_top`：le_of_iSup_eq
_top {I J : X.IdealSheafData} {ι : Type*} (U : ι -> X.affineOpens) (hU : ⨆ i, (U
 i).1 = ⊤) (H : forall i, I.ideal (U i) <= J.id…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma ext_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (H : ∀ i, I.ideal (U i) = J.ideal (U i)) :
    I = J :=
  (le_of_iSup_eq_top U hU (by aesop)).antisymm (le_of_iSup_eq_top U hU (by aesop))

end map_ideal

section support

/-
**AlgebraicGeometry.Scheme.IdealSheafData.mem_supportSet_iff** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：mem_supportSet_iff {I : IdealSheafData X} {x} : x in I.supportSet ↔ forall
 U, x in X.zeroLocus (U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_eq_iInter_zeroLocus`：
∀ {X : AlgebraicGeometry.Scheme} (self : X.IdealSheafData), self.supportSet = ⋂ 
U, X.zeroLocus ↑(self.ideal U)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
lemma mem_supportSet_iff {I : IdealSheafData X} {x} :
    x ∈ I.supportSet ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter
/-
**AlgebraicGeometry.Scheme.IdealSheafData.supportSet_subset_zeroLocus** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：supportSet_subset_zeroLocus (I : IdealSheafData X) (U : X.affineOpens) : I
.supportSet subseteq X.zeroLocus (U
参数：I : IdealSheafData X；U : X.affineOpens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_eq_iInter_zeroLocus`：
∀ {X : AlgebraicGeometry.Scheme} (self : X.IdealSheafData), self.supportSet = ⋂ 
U, X.zeroLocus ↑(self.ideal U)
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
lemma supportSet_subset_zeroLocus (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet ⊆ X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus.trans_subset (Set.iInter_subset _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.zeroLocus_inter_subset_supportSet** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpen
s) : X.zeroLocus (U
参数：I : IdealSheafData X；U : X.affineOpens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_eq_iInter_zeroLocus`：
∀ {X : AlgebraicGeometry.Scheme} (self : X.IdealSheafData), self.supportSet = ⋂ 
U, X.zeroLocus ↑(self.ideal U)
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `Codisjoint.left_le_of_le_inf_right`：Codisjoint.left_le_of_le_inf_right (
h : a ⊓ b <= c) (hd : Codisjoint b c) : a <= c
· 使用定理 `Codisjoint.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] ⦃a b : α⦄, Codisjoint a b → Codisjoint b a
· 使用引理 `AlgebraicGeometry.Scheme.codisjoint_zeroLocus`：codisjoint_zeroLocus {U :
 X.Opens} (s : Set Γ(X, U)) : Codisjoint (X.zeroLocus s) U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgebraicGeometry.exists_basicOpen_le_affine_inter`：∀ {X : AlgebraicGeom
etry.Scheme} {U : X.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ {V : X.Op
ens},       AlgebraicGeometry.IsAffineOp…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`：map_ideal {U V : X.af
fineOpens} (h : U <= V) : (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = 
I.ideal U
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen`：∀ {X : Alge
braicGeometry.Scheme} (self : X.IdealSheafData) (U : ↑X.affineOpens)   (f : ↑(X.
presheaf.obj (Opposite.op ↑U))),   Ideal.map (Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
（共 49 条，此处仅展示前 30 条）
-/
lemma zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpens) :
    X.zeroLocus (U := U.1) (I.ideal U) ∩ U ⊆ I.supportSet := by
  rw [I.supportSet_eq_iInter_zeroLocus]
  refine Set.subset_iInter fun V ↦ ?_
  apply (X.codisjoint_zeroLocus (U := V) (I.ideal V)).symm.left_le_of_le_inf_right
  rintro x ⟨⟨hx, hxU⟩, hxV⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx ⊢
  intro s hfU hxs
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have inst := U.2.isLocalization_basicOpen f
  have := (I.map_ideal (U := X.affineBasicOpen f) (hfg.trans_le (X.basicOpen_le g))).le
    (Ideal.mem_map_of_mem _ hfU)
  rw [← I.map_ideal_basicOpen] at this
  obtain ⟨⟨s', ⟨_, n, rfl⟩⟩, hs'⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (.powers f) Γ(X, X.basicOpen f)).mp this
  apply_fun (x ∈ X.basicOpen ·) at hs'
  refine hx s' s'.2 ?_
  cases n <;>
    simpa [RingHom.algebraMap_toAlgebra, ← hfg, hxf, hxs, Scheme.basicOpen_pow] using hs'
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mem_supportSet_iff_of_mem** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：mem_supportSet_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (
hxU : x in U.1) : x in I.supportSet ↔ x in X.zeroLocus (U
参数：hxU : x in U.1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_eq_iInter_zeroLocus`：
∀ {X : AlgebraicGeometry.Scheme} (self : X.IdealSheafData), self.supportSet = ⋂ 
U, X.zeroLocus ↑(self.ideal U)
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.zeroLocus_inter_subset_supportSe
t`：zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpens) 
: X.zeroLocus (U
-/
lemma mem_supportSet_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x ∈ U.1) :
    x ∈ I.supportSet ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  ⟨I.supportSet_eq_iInter_zeroLocus ▸ fun h ↦ Set.iInter_subset _ U h,
    fun h ↦ I.zeroLocus_inter_subset_supportSet U ⟨h, hxU⟩⟩
/-
**AlgebraicGeometry.Scheme.IdealSheafData.supportSet_inter** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：supportSet_inter (I : IdealSheafData X) (U : X.affineOpens) : I.supportSet
 inter U = X.zeroLocus (U
参数：I : IdealSheafData X；U : X.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.mem_supportSet_iff_of_mem`：mem_s
upportSet_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x in 
U.1) : x in I.supportSet ↔ x in X.zeroLocus (U
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma supportSet_inter (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U := by
  ext x
  by_cases hxU : x ∈ U.1
  · simp [hxU, mem_supportSet_iff_of_mem hxU]
  · simp [hxU]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.isClosed_supportSet** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：isClosed_supportSet (I : IdealSheafData X) : IsClosed I.supportSet
参数：I : IdealSheafData X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage`：isClosed_iff_coe
_preimage {s : Set β} : IsClosed s ↔ forall i, IsClosed ((↑) ⁻¹' s : Set (U i))
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_isClosed`：zeroLocus_isClosed {U : X.O
pens} (s : Set Γ(X, U)) : IsClosed (X.zeroLocus s)
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_inter`：supportSet_int
er (I : IdealSheafData X) (U : X.affineOpens) : I.supportSet inter U = X.zeroLoc
us (U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isClosed_supportSet (I : IdealSheafData X) : IsClosed I.supportSet := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set.image_preimage_eq_inter_range, I.supportSet_inter]

/-- The support of an ideal sheaf. Also see `IdealSheafData.mem_support_iff_of_mem`. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support : Closeds X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.isClosed_supportSet`：isClosed_su
pportSet (I : IdealSheafData X) : IsClosed I.supportSet

--- 原说明 ---
The support of an ideal sheaf. Also see `IdealSheafData.mem_support_iff_of_mem`.
-/
def support : Closeds X := ⟨I.supportSet, I.isClosed_supportSet⟩
/-
**AlgebraicGeometry.Scheme.IdealSheafData.coe_support_eq_eq_iInter_zeroLocus** 是
 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：coe_support_eq_eq_iInter_zeroLocus : (I.support : Set X) = ⋂ U, X.zeroLocu
s (U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_eq_iInter_zeroLocus`：
∀ {X : AlgebraicGeometry.Scheme} (self : X.IdealSheafData), self.supportSet = ⋂ 
U, X.zeroLocus ↑(self.ideal U)
-/
lemma coe_support_eq_eq_iInter_zeroLocus :
    (I.support : Set X) = ⋂ U, X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mem_supportSet_iff_mem_support** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {I : X.IdealSheafData} {x : ↥X}, x ∈ I.su
pportSet ↔ x ∈ I.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_supportSet_iff_mem_support {I : IdealSheafData X} {x} :
    x ∈ I.supportSet ↔ x ∈ I.support := .rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：mem_support_iff {I : IdealSheafData X} {x} : x in I.support ↔ forall U, x 
in X.zeroLocus (U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_eq_iInter_zeroLocus`：
∀ {X : AlgebraicGeometry.Scheme} (self : X.IdealSheafData), self.supportSet = ⋂ 
U, X.zeroLocus ↑(self.ideal U)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
lemma mem_support_iff {I : IdealSheafData X} {x} :
    x ∈ I.support ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：mem_support_iff_of_mem {I : IdealSheafData X} {x : X} {U : X.affineOpens} 
(h : x in U.1) : x in I.support ↔ x in X.zeroLocus (U
参数：h : x in U.1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_inter`：supportSet_int
er (I : IdealSheafData X) (U : X.affineOpens) : I.supportSet inter U = X.zeroLoc
us (U
-/
lemma mem_support_iff_of_mem {I : IdealSheafData X} {x : X} {U : X.affineOpens} (h : x ∈ U.1) :
    x ∈ I.support ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) := by
  simpa [-mem_zeroLocus_iff, h] using congr(x ∈ $(I.supportSet_inter U))
/-
**AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：coe_support_inter (I : IdealSheafData X) (U : X.affineOpens) : (I.support 
: Set X) inter U = X.zeroLocus (U
参数：I : IdealSheafData X；U : X.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.supportSet_inter`：supportSet_int
er (I : IdealSheafData X) (U : X.affineOpens) : I.supportSet inter U = X.zeroLoc
us (U
-/
lemma coe_support_inter (I : IdealSheafData X) (U : X.affineOpens) :
    (I.support : Set X) ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U :=
  I.supportSet_inter U

/-- Custom simps projection for `IdealSheafData`. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.Simps.coe_support** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData.Simps`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → X.IdealSheafData → Set ↥X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Custom simps projection for `IdealSheafData`.
-/
def Simps.coe_support : Set X := I.support

initialize_simps_projections IdealSheafData (supportSet → coe_support, as_prefix coe_support)

/-- A useful constructor of `IdealSheafData`
with the condition on `supportSet` being easier to check. -/
@[simps ideal coe_support]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mkOfMemSupportIff** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：mkOfMemSupportIff (ideal : forall U : X.affineOpens, Ideal Γ(X, U)) (map_i
deal_basicOpen : forall (U : X.affineOpens) (f : Γ(X, U)), (ideal U).map (X.pres
heaf.map (homOfLE <| X.basicOpen_le f).op).hom = ideal (X.affineBasicOpen f)) (s
upportSet : Set X) (supportSet_inter : forall U : X.affineOpens, forall x in U.1
, x in supportSet ↔ x in X.zeroLocus (U
参数：ideal : forall U : X.affineOpens, Ideal Γ(X, U)；map_ideal_basicOpen : forall 
(U : X.affineOpens) (f : Γ(X, U)), (ideal U).map (X.presheaf.map (homOfLE <| X.b
asicOpen_le f).op).hom = ideal (X.affineBasicOpen f)；supportSet : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A useful constructor of `IdealSheafData`
with the condition on `supportSet` being easier to check.
-/
def mkOfMemSupportIff
    (ideal : ∀ U : X.affineOpens, Ideal Γ(X, U))
    (map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
      (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
        ideal (X.affineBasicOpen f))
    (supportSet : Set X)
    (supportSet_inter :
      ∀ U : X.affineOpens, ∀ x ∈ U.1, x ∈ supportSet ↔ x ∈ X.zeroLocus (U := U.1) (ideal U)) :
    X.IdealSheafData where
  ideal := ideal
  map_ideal_basicOpen := map_ideal_basicOpen
  supportSet := supportSet
  supportSet_eq_iInter_zeroLocus := by
    let I' : X.IdealSheafData := { ideal := ideal, map_ideal_basicOpen := map_ideal_basicOpen }
    change supportSet = I'.supportSet
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (supportSet_inter ⟨U, hU⟩ x hxU).trans
      (I'.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).symm

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_top** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_top : support (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma support_top : support (X := X) ⊤ = ⊥ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_bot** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_bot : support (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma support_bot : support (X := X) ⊥ = ⊤ := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_antitone** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_antitone : Antitone (support (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_eq_eq_iInter_zeroLoc
us`：coe_support_eq_eq_iInter_zeroLocus : (I.support : Set X) = ⋂ U, X.zeroLocus 
(U
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_mono`：zeroLocus_mono {U : X.Opens} {s
 t : Set Γ(X, U)} (h : s subseteq t) : X.zeroLocus t subseteq X.zeroLocus s
-/
lemma support_antitone : Antitone (support (X := X)) := by
  intro I J h
  rw [← SetLike.coe_subset_coe, I.coe_support_eq_eq_iInter_zeroLocus,
    J.coe_support_eq_eq_iInter_zeroLocus]
  exact Set.iInter_mono fun U ↦ X.zeroLocus_mono (h U)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_eq_bot_iff : support I = ⊥ ↔ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_image_zeroLocus`：∀ {X : Algebrai
cGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)   (s : S
et ↑(X.presheaf.obj (Opposite.op U))), ⇑hU.fr…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.zeroLocus_inter_subset_supportSe
t`：zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpens) 
: X.zeroLocus (U
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.zeroLocus_empty_iff_eq_top`：zeroLocus_empty_iff_eq_top {I 
: Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma support_eq_bot_iff : support I = ⊥ ↔ I = ⊤ := by
  refine ⟨fun H ↦ top_le_iff.mp fun U ↦ ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_supportSet I U).trans H.le)
  simp only [Set.subset_empty_iff, Set.image_eq_empty, Closeds.coe_bot] at this
  simp [PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp this]

end support

section Semiring

variable (I J K : X.IdealSheafData)

/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero X.IdealSheafData where zero := ⊥
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One X.IdealSheafData where one := ⊤
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add X.IdealSheafData where add := (· ⊔ ·)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul X.IdealSheafData where
  mul I J := mkOfMemSupportIff (I.ideal * J.ideal) (by simp [Ideal.map_mul, map_ideal_basicOpen])
    (I.supportSet ∪ J.supportSet) fun U x hxU ↦ by
    simp [-mem_zeroLocus_iff, zeroLocus_mul, mem_support_iff_of_mem hxU]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow X.IdealSheafData ℕ where
  pow I n := mkOfMemSupportIff (I.ideal ^ n) (by simp [Ideal.map_pow, map_ideal_basicOpen])
    (if n = 0 then ∅ else I.supportSet) fun U x hxU ↦ .symm <| by
    induction n <;> simp_all [-mem_zeroLocus_iff, zeroLocus_mul,
      pow_succ, mem_support_iff_of_mem hxU]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I J : X.IdealSheafData), (I * J).ideal =
 I.ideal * J.ideal
参数：I J : X.IdealSheafData；I * J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ideal_mul : (I * J).ideal = I.ideal * J.ideal := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_mul** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I J : X.IdealSheafData), (I * J).support
 = I.support ⊔ J.support
参数：I J : X.IdealSheafData；I * J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma support_mul : (I * J).support = I.support ⊔ J.support := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData) (n : ℕ), (I ^ n).i
deal = I.ideal ^ n
参数：I : X.IdealSheafData；n : ℕ；I ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ideal_pow (n : ℕ) : (I ^ n).ideal = I.ideal ^ n := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_pow_succ** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData) (n : ℕ), (I ^ (n +
 1)).support = I.support
参数：I : X.IdealSheafData；n : ℕ；I ^ (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma support_pow_succ (n : ℕ) : (I ^ (n + 1)).support = I.support := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_pow** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_pow (n : Nat) (hn : n != 0) : (I ^ n).support = I.support
参数：n : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma support_pow (n : ℕ) (hn : n ≠ 0) : (I ^ n).support = I.support := by cases n <;> simp_all
/-
**AlgebraicGeometry.Scheme.IdealSheafData.top_mul** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), ⊤ * I = I
参数：I : X.IdealSheafData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.top_mul`：top_mul : ⊤ * I = I
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma top_mul : ⊤ * I = I := by ext; simp
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mul_top** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), I * ⊤ = I
参数：I : X.IdealSheafData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mul_top : I * ⊤ = I := by ext; simp
/-
**AlgebraicGeometry.Scheme.IdealSheafData.bot_mul** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), ⊥ * I = ⊥
参数：I : X.IdealSheafData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.bot_mul`：bot_mul : ⊥ * M = ⊥
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma bot_mul : ⊥ * I = ⊥ := by ext; simp
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), I * ⊥ = ⊥
参数：I : X.IdealSheafData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mul_bot : I * ⊥ = ⊥ := by ext; simp
/-
**AlgebraicGeometry.Scheme.IdealSheafData.mul_inf** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：mul_inf : I * (J ⊔ K) = I * J ⊔ I * K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
lemma mul_inf : I * (J ⊔ K) = I * J ⊔ I * K := by ext U : 2; exact mul_add _ _ _
/-
**AlgebraicGeometry.Scheme.IdealSheafData.inf_mul** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：inf_mul : (I ⊔ J) * K = I * K ⊔ J * K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma inf_mul : (I ⊔ J) * K = I * K ⊔ J * K := by ext U : 2; exact add_mul _ _ _
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IdemCommSemiring X.IdealSheafData where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc _ _ _ := IdealSheafData.ext (mul_assoc _ _ _)
  mul_comm _ _ := IdealSheafData.ext (mul_comm _ _)
  zero_mul := bot_mul
  mul_zero := mul_bot
  one_mul := top_mul
  mul_one := mul_top
  nsmul := nsmulRec
  left_distrib := mul_inf
  right_distrib := inf_mul
  npow n I := I ^ n
  npow_zero _ := by ext; simp [show (1 : X.IdealSheafData) = ⊤ from rfl]
  npow_succ _ _ := by ext; rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedRing X.IdealSheafData where

/-! We follow `Ideal` and set the simp normal form to be `⊥` and `⊤` and `⊔`. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.zero_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}, 0 = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We follow `Ideal` and set the simp normal form to be `⊥` and `⊤` and `⊔`.
-/
@[simp] lemma zero_eq_bot : (0 : X.IdealSheafData) = ⊥ := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.one_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}, 1 = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We follow `Ideal` and set the simp normal form to be `⊥` and `⊤` and `⊔`.
-/
@[simp] lemma one_eq_top : (1 : X.IdealSheafData) = ⊤ := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.add_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I J : X.IdealSheafData), I + J = I ⊔ J
参数：I J : X.IdealSheafData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We follow `Ideal` and set the simp normal form to be `⊥` and `⊤` and `⊔`.
-/
@[simp] lemma add_eq_sup : I + J = I ⊔ J := rfl

end Semiring

section IsAffine

/-- The ideal sheaf induced by an ideal of the global sections. -/
@[simps! ideal coe_support]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ofIdealTop (I : Ideal Γ(X, ⊤)) : IdealSheafData X
参数：I : Ideal Γ(X, ⊤)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal sheaf induced by an ideal of the global sections.
-/
def ofIdealTop (I : Ideal Γ(X, ⊤)) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ I.map (X.presheaf.map (homOfLE le_top).op).hom)
    (fun U f ↦ by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (X.zeroLocus (U := ⊤) I)
    (fun U x hxU ↦ by
      simp only [Ideal.map, zeroLocus_span, zeroLocus_map, Set.mem_union, Set.mem_compl_iff,
        SetLike.mem_coe, hxU, not_true_eq_false, iff_self_or, IsEmpty.forall_iff])
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_of_isAffine** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_of_isAffine [IsAffine X] {I J : IdealSheafData X} (H : I.ideal ⟨⊤, isAf
fineOpen_top X⟩ <= J.ideal ⟨⊤, isAffineOpen_top X⟩) : I <= J
参数：H : I.ideal ⟨⊤, isAffineOpen_top X⟩ <= J.ideal ⟨⊤, isAffineOpen_top X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`：map_ideal {U V : X.af
fineOpens} (h : U <= V) : (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = 
I.ideal U
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
-/
lemma le_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ ≤ J.ideal ⟨⊤, isAffineOpen_top X⟩) : I ≤ J := by
  intro U
  rw [← map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) I (le_top (a := U.1)),
    ← map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) J (le_top (a := U.1))]
  exact Ideal.map_mono H
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：ext_of_isAffine [IsAffine X] {I J : IdealSheafData X} (H : I.ideal ⟨⊤, isA
ffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J
参数：H : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_of_isAffine`：le_of_isAffine [
IsAffine X] {I J : IdealSheafData X} (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ <= J.i
deal ⟨⊤, isAffineOpen_top X⟩) : I <= J
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma ext_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  (le_of_isAffine H.le).antisymm (le_of_isAffine H.ge)

/-- Over affine schemes, ideal sheaves are in bijection with ideals of the global sections. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：equivOfIsAffine [IsAffine X] : IdealSheafData X ≃+*o Ideal Γ(X, ⊤) where t
oFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)

--- 原说明 ---
Over affine schemes, ideal sheaves are in bijection with ideals of the global se
ctions.
-/
def equivOfIsAffine [IsAffine X] : IdealSheafData X ≃+*o Ideal Γ(X, ⊤) where
  toFun := (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp
  map_mul' := by simp
  map_add' := by simp
  map_le_map_iff' := ⟨le_of_isAffine, (· _)⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine_apply** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：equivOfIsAffine_apply [IsAffine X] (I : IdealSheafData X) : equivOfIsAffin
e I = I.ideal ⟨⊤, isAffineOpen_top X⟩
参数：I : IdealSheafData X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma equivOfIsAffine_apply [IsAffine X] (I : IdealSheafData X) :
    equivOfIsAffine I = I.ideal ⟨⊤, isAffineOpen_top X⟩ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine_symm_apply** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：equivOfIsAffine_symm_apply [IsAffine X] (I : Ideal Γ(X, ⊤)) : equivOfIsAff
ine.symm I = ofIdealTop I
参数：I : Ideal Γ(X, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma equivOfIsAffine_symm_apply [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    equivOfIsAffine.symm I = ofIdealTop I := rfl

end IsAffine

section ofIsClosed

open _root_.PrimeSpectrum TopologicalSpace

/-- The radical of an ideal sheaf. -/
@[simps! ideal]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.radical** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：radical (I : IdealSheafData X) : IdealSheafData X
参数：I : IdealSheafData X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radical of an ideal sheaf.
-/
def radical (I : IdealSheafData X) : IdealSheafData X :=
  mkOfMemSupportIff
  (fun U ↦ (I.ideal U).radical)
  (fun U f ↦
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLocalization.map_radical (.powers f) Γ(X, X.basicOpen f) (I.ideal U)).trans
      congr($(I.map_ideal_basicOpen U f).radical))
  I.supportSet
  (fun U x hx ↦ by
    simp only [mem_supportSet_iff_of_mem hx, AlgebraicGeometry.Scheme.zeroLocus_radical])

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_radical** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：support_radical (I : IdealSheafData X) : I.radical.support = I.support
参数：I : IdealSheafData X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma support_radical (I : IdealSheafData X) : I.radical.support = I.support := rfl

/-- The nilradical of a scheme. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData._root_.AlgebraicGeometry.Scheme.nilrad
ical** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nilradical of a scheme.
-/
def _root_.AlgebraicGeometry.Scheme.nilradical (X : Scheme.{u}) : IdealSheafData X :=
  .radical ⊥

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData._root_.AlgebraicGeometry.Scheme.suppor
t_nilradical** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.Scheme.support_nilradical (X : Scheme.{u}) :
    X.nilradical.support = ⊤ := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_radical** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_radical : I <= I.radical
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
-/
lemma le_radical : I ≤ I.radical := fun _ ↦ Ideal.le_radical

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.radical_top** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：radical_top : radical (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_radical`：le_radical : I <= I.
radical
-/
lemma radical_top : radical (X := X) ⊤ = ⊤ := top_le_iff.mp (le_radical _)
/-
**AlgebraicGeometry.Scheme.IdealSheafData.radical_bot** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：radical_bot : radical ⊥ = nilradical X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma radical_bot : radical ⊥ = nilradical X := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.radical_sup** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：radical_sup {I J : IdealSheafData X} : radical (I ⊔ J) = radical (radical 
I ⊔ radical J)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.radical_sup`：radical_sup : radical (I ⊔ J) = radical (radical I ⊔ 
radical J)
-/
lemma radical_sup {I J : IdealSheafData X} :
    radical (I ⊔ J) = radical (radical I ⊔ radical J) := by
  ext U : 2
  exact (Ideal.radical_sup (I.ideal U) (J.ideal U))

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.radical_inf** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：radical_inf {I J : IdealSheafData X} : radical (I ⊓ J) = radical I ⊓ radic
al J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal`：∀ {X : AlgebraicG
eometry.Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens), I.radical.ideal U =
 (I.ideal U).radical
· 使用定理 `Ideal.radical_inf`：radical_inf : radical (I ⊓ J) = radical I ⊓ radical J
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma radical_inf {I J : IdealSheafData X} :
    radical (I ⊓ J) = radical I ⊓ radical J := by
  ext U : 2
  simp only [radical_ideal, ideal_inf, Pi.inf_apply, Ideal.radical_inf]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.radical_mul** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：radical_mul {I J : IdealSheafData X} : radical (I * J) = radical I ⊓ radic
al J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal`：∀ {X : AlgebraicG
eometry.Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens), I.radical.ideal U =
 (I.ideal U).radical
· 使用定理 `Ideal.radical_mul`：radical_mul : radical (I * J) = radical I ⊓ radical J
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma radical_mul {I J : IdealSheafData X} :
    radical (I * J) = radical I ⊓ radical J := by
  ext U : 2
  simp only [radical_ideal, ideal_mul, Pi.mul_apply, Ideal.radical_mul, ideal_inf, Pi.inf_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The vanishing ideal sheaf of a closed set,
which is the largest ideal sheaf whose support is equal to it.
The reduced induced scheme structure on the closed set is the quotient of this ideal. -/
@[simps! ideal coe_support]
noncomputable nonrec def vanishingIdeal (Z : Closeds X) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ vanishingIdeal (U.2.fromSpec ⁻¹' Z))
    (fun U f ↦ by
      let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        suffices ∀ p, (X.affineBasicOpen f).2.fromSpec p ∈ Z → F.hom x ∈ p.asIdeal by
          simpa [PrimeSpectrum.mem_vanishingIdeal] using! this
        intro x hxZ
        refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx
          (Spec.map (X.presheaf.map (homOfLE _).op) x) ?_
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply,
          IsAffineOpen.map_fromSpec _ (X.affineBasicOpen f).2]
      · let : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) := F.hom.toAlgebra
        have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
          U.2.isLocalization_of_eq_basicOpen _ _ rfl
        intro x hx
        dsimp only at hx ⊢
        have : Topology.IsOpenEmbedding (Spec.map F) :=
          localization_away_isOpenEmbedding Γ(X, X.basicOpen f) f
        rw [← U.2.map_fromSpec (X.affineBasicOpen f).2 (homOfLE (X.basicOpen_le f)).op,
          Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hx
        generalize U.2.fromSpec ⁻¹' Z = Z' at hx ⊢
        replace hx : x ∈ vanishingIdeal (Spec.map F ⁻¹' Z') := hx
        obtain ⟨I, hI, e⟩ :=
          (isClosed_iff_zeroLocus_radical_ideal _).mp (isClosed_closure (s := Z'))
        rw [← vanishingIdeal_closure,
          ← this.isOpenMap.preimage_closure_eq_closure_preimage this.continuous, e] at hx
        rw [← vanishingIdeal_closure, e]
        erw [preimage_comap_zeroLocus] at hx
        rwa [← PrimeSpectrum.zeroLocus_span, ← Ideal.map, vanishingIdeal_zeroLocus_eq_radical,
          ← RingHom.algebraMap_toAlgebra (X.presheaf.map _).hom,
          ← IsLocalization.map_radical (.powers f), ← vanishingIdeal_zeroLocus_eq_radical] at hx)
    Z
    (fun U x hxU ↦ by
      trans x ∈ X.zeroLocus (U := U.1) (vanishingIdeal (U.2.fromSpec ⁻¹' Z)) ∩ U.1
      · rw [← U.2.fromSpec_image_zeroLocus, zeroLocus_vanishingIdeal_eq_closure,
          ← U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
            U.2.fromSpec.continuous,
          Set.image_preimage_eq_inter_range, Z.isClosed.closure_eq, IsAffineOpen.range_fromSpec]
        simp [hxU]
      · simp [hxU])

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal** 是 M
athlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} : 
Z <= I.support ↔ I <= vanishingIdeal Z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_ideal`：∀ {X : Alg
ebraicGeometry.Scheme} (Z : TopologicalSpace.Closeds ↥X) (U : ↑X.affineOpens),  
 (AlgebraicGeometry.Scheme.IdealSheafData.vanishin…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter`：coe_support_i
nter (I : IdealSheafData X) (U : X.affineOpens) : (I.support : Set X) inter U = 
X.zeroLocus (U
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_image_zeroLocus`：∀ {X : Algebrai
cGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)   (s : S
et ↑(X.presheaf.obj (Opposite.op U))), ⇑hU.fr…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} :
    Z ≤ I.support ↔ I ≤ vanishingIdeal Z := by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans ∀ U : X.affineOpens, (Z : Set X) ∩ U ⊆ I.support ∩ U
  · refine ⟨fun H U x hx ↦ ⟨H hx.1, hx.2⟩, fun H x hx ↦ ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (H ⟨U, hU⟩ ⟨hx, hxU⟩).1
  refine forall_congr' fun U ↦ ?_
  rw [coe_support_inter, ← Set.image_subset_image_iff U.2.fromSpec.isOpenEmbedding.injective,
    Set.image_preimage_eq_inter_range, IsAffineOpen.fromSpec_image_zeroLocus,
    IsAffineOpen.range_fromSpec]

/-- `support` and `vanishingIdeal` forms a Galois connection.
This is the global version of `PrimeSpectrum.gc`. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.gc** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.IdealSheafData`。
形式化陈述：gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (van
ishingIdeal ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
`：le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} : Z <=
 I.support ↔ I <= vanishingIdeal Z

--- 原说明 ---
`support` and `vanishingIdeal` forms a Galois connection.
This is the global version of `PrimeSpectrum.gc`.
-/
lemma gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
  fun _ _ ↦ le_support_iff_le_vanishingIdeal
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_antimono** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：vanishingIdeal_antimono {S T : Closeds X} (h : S <= T) : vanishingIdeal T 
<= vanishingIdeal S
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
lemma vanishingIdeal_antimono {S T : Closeds X} (h : S ≤ T) : vanishingIdeal T ≤ vanishingIdeal S :=
  gc.monotone_u h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：vanishingIdeal_support {I : IdealSheafData X} : vanishingIdeal I.support =
 I.radical
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_image_zeroLocus`：∀ {X : Algebrai
cGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)   (s : S
et ↑(X.presheaf.obj (Opposite.op U))), ⇑hU.fr…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter`：coe_support_i
nter (I : IdealSheafData X) (U : X.affineOpens) : (I.support : Set X) inter U = 
X.zeroLocus (U
-/
lemma vanishingIdeal_support {I : IdealSheafData X} :
    vanishingIdeal I.support = I.radical := by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
    IsAffineOpen.fromSpec_image_zeroLocus, coe_support_inter]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_bot** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}, AlgebraicGeometry.Scheme.IdealSheafData.
vanishingIdeal ⊥ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma vanishingIdeal_bot : vanishingIdeal (X := X) ⊥ = ⊤ := gc.u_top
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}, AlgebraicGeometry.Scheme.IdealSheafData.
vanishingIdeal ⊤ = X.nilradical
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.support_bot`：support_bot : suppo
rt (X
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support`：vanishin
gIdeal_support {I : IdealSheafData X} : vanishingIdeal I.support = I.radical
· 使用定理 `AlgebraicGeometry.Scheme.nilradical.eq_1`：∀ (X : AlgebraicGeometry.Schem
e), X.nilradical = ⊥.radical
-/
@[simp] lemma vanishingIdeal_top : vanishingIdeal (X := X) ⊤ = X.nilradical := by
  rw [← support_bot, vanishingIdeal_support, nilradical]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_iSup** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {ι : Sort u_1} (Z : ι → TopologicalSpace.
Closeds ↥X),   AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (iSup Z) =
     ⨅ i, AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (Z i)
参数：Z : ι → TopologicalSpace.Closeds ↥X；iSup Z；Z i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma vanishingIdeal_iSup {ι : Sort*} (Z : ι → Closeds X) :
    vanishingIdeal (iSup Z) = ⨅ i, vanishingIdeal (Z i) := gc.u_iInf
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_sSup** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (Z : Set (TopologicalSpace.Closeds ↥X)), 
  AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (sSup Z) =     ⨅ z ∈ Z,
 AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal z
参数：Z : Set (TopologicalSpace.Closeds ↥X)；sSup Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma vanishingIdeal_sSup (Z : Set (Closeds X)) :
    vanishingIdeal (sSup Z) = ⨅ z ∈ Z, vanishingIdeal z := gc.u_sInf
/-
**AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_sup** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (Z Z' : TopologicalSpace.Closeds ↥X),   A
lgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (Z ⊔ Z') =     AlgebraicGe
ometry.Scheme.IdealSheafData.vanishingIdeal Z ⊓ AlgebraicGeometry.Scheme.IdealSh
eafData.vanishingIdeal Z'
参数：Z Z' : TopologicalSpace.Closeds ↥X；Z ⊔ Z'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma vanishingIdeal_sup (Z Z' : TopologicalSpace.Closeds X) :
    vanishingIdeal (Z ⊔ Z') = vanishingIdeal Z ⊓ vanishingIdeal Z' := gc.u_inf
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_sup** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I J : X.IdealSheafData), (I ⊔ J).support
 = I.support ⊓ J.support
参数：I J : X.IdealSheafData；I ⊔ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma support_sup (I J : X.IdealSheafData) :
    (I ⊔ J).support = I.support ⊓ J.support := gc.l_sup
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_iSup** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {ι : Sort u_1} (I : ι → X.IdealSheafData)
, (iSup I).support = ⨅ i, (I i).support
参数：I : ι → X.IdealSheafData；iSup I；I i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma support_iSup {ι : Sort*} (I : ι → X.IdealSheafData) :
    (iSup I).support = ⨅ i, (I i).support := gc.l_iSup
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_sSup** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (I : Set X.IdealSheafData), (sSup I).supp
ort = ⨅ i ∈ I, i.support
参数：I : Set X.IdealSheafData；sSup I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.gc`：gc : @GaloisConnection X.Ide
alSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
-/
@[simp] lemma support_sSup (I : Set X.IdealSheafData) :
    (sSup I).support = ⨅ i ∈ I, i.support := gc.l_sSup

end ofIsClosed

end IdealSheafData

section IsReduced

/-
**AlgebraicGeometry.Scheme.nilradical_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：nilradical_eq_bot [IsReduced X] : X.nilradical = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal`：∀ {X : AlgebraicG
eometry.Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens), I.radical.ideal U =
 (I.ideal U).radical
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.radical_eq_iff`：radical_eq_iff : I.radical = I ↔ I.IsRadical
· 使用引理 `Ideal.isRadical_bot`：isRadical_bot [IsReduced R] : (⊥ : Ideal R).IsRadic
al
· 使用定理 `AlgebraicGeometry.IsReduced.component_reduced`：∀ {X : AlgebraicGeometry.
Scheme} [self : AlgebraicGeometry.IsReduced X] (U : X.Opens),   IsReduced ↑(X.pr
esheaf.obj (Opposite.op U))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nilradical_eq_bot [IsReduced X] : X.nilradical = ⊥ := by
  ext; simp [nilradical, Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsReduced X] {I : X.Id
ealSheafData}, I.support = ⊤ ↔ I = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
`：le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} : Z <=
 I.support ↔ I <= vanishingIdeal Z
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top`：∀ {X : Algeb
raicGeometry.Scheme}, AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⊤ =
 X.nilradical
· 使用引理 `AlgebraicGeometry.Scheme.nilradical_eq_bot`：nilradical_eq_bot [IsReduced
 X] : X.nilradical = ⊥
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IdealSheafData.support_eq_top_iff [IsReduced X] {I : X.IdealSheafData} :
    I.support = ⊤ ↔ I = ⊥ := by
  rw [← top_le_iff, le_support_iff_le_vanishingIdeal,
    vanishingIdeal_top, nilradical_eq_bot, le_bot_iff]

end IsReduced

section ker

open IdealSheafData

variable {Y Z : Scheme.{u}}

/-- The kernel of a morphism,
defined as the largest (quasi-coherent) ideal sheaf contained in the component-wise kernel.
This is usually only well-behaved when `f` is quasi-compact. -/
/-
**AlgebraicGeometry.Scheme.Hom.ker** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.Hom Y → Y.IdealSheafData
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a morphism,
defined as the largest (quasi-coherent) ideal sheaf contained in the component-w
ise kernel.
This is usually only well-behaved when `f` is quasi-compact.
-/
def Hom.ker (f : X.Hom Y) : IdealSheafData Y :=
  ofIdeals fun U ↦ RingHom.ker (f.app U).hom
/-
**AlgebraicGeometry.Scheme.Hom.ideal_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.Hom Y) (U : ↑Y.affineOpens),   f
.ker.ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (f.app ↑U))
参数：f : X.Hom Y；U : ↑Y.affineOpens；CommRingCat.Hom.hom (f.app ↑U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le`：ideal_ofIdeal
s_le (I : forall U : X.affineOpens, Ideal Γ(X, U)) : (ofIdeals I).ideal <= I
-/
lemma Hom.ideal_ker_le (f : X.Hom Y) (U : Y.affineOpens) :
    f.ker.ideal U ≤ RingHom.ker (f.app U).hom :=
  ideal_ofIdeals_le _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.ker_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.Hom Y) [AlgebraicGeometry.QuasiC
ompact f] (U : ↑Y.affineOpens),   f.ker.ideal U = RingHom.ker (CommRingCat.Hom.h
om (f.app ↑U))
参数：f : X.Hom Y；U : ↑Y.affineOpens；CommRingCat.Hom.hom (f.app ↑U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `RingHom.ker.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomCl
ass F R S] (…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.naturality`：naturality (i : op U' ⟶ op U) :
 Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map 
i.unop).op
· 使用定理 `Ideal.ker_le_comap`：ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <
= comap f K
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_mem_map_algebraMap_iff`：∀ {R : Type u_1} [inst : Comm
Semiring R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] [inst_3 : IsLoc…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isC
ompact`：exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme
.{u}) {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U)) (H : x |_ (…
· 使用定理 `AlgebraicGeometry.QuasiCompact.isCompact_preimage`：∀ {X Y : AlgebraicGeo
metry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.QuasiCompact f] (U : Set ↥Y)
,   IsOpen U → IsCompact U → IsCompact …
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
（共 34 条，此处仅展示前 30 条）
-/
lemma Hom.ker_apply (f : X.Hom Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := by
  let I : IdealSheafData Y := ⟨fun U ↦ RingHom.ker (f.app U).hom, ?_, _, rfl⟩
  · exact congr($(ofIdeals_ideal I).ideal U)
  intro U s
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    simp_rw [RingHom.comap_ker, ← CommRingCat.hom_comp, Scheme.affineBasicOpen_coe, f.naturality,
      CommRingCat.hom_comp, ← RingHom.comap_ker]
    exact Ideal.ker_le_comap _ hx
  · intro x hx
    have := U.2.isLocalization_basicOpen s
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    refine (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ?_
    suffices ∃ (V : X.Opens) (hV : V = X.basicOpen ((f.app U).hom s)),
        letI := hV.trans_le (X.basicOpen_le _); ((f.app U).hom x |_ V) = 0 by
      obtain ⟨_, rfl, H⟩ := this
      obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        X (U := f ⁻¹ᵁ U) (QuasiCompact.isCompact_preimage (f := f) _ U.1.2 U.2.isCompact)
        (f.app U x) (f.app U s) H
      exact ⟨_, ⟨n, rfl⟩, by simpa using hn⟩
    refine ⟨f ⁻¹ᵁ Y.basicOpen s, by simp, ?_⟩
    replace hx : (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op ≫ f.app _).hom x = 0 := by
      trans (f.app (Y.basicOpen s)).hom (algebraMap Γ(Y, U) _ x)
      · simp [-NatTrans.naturality, RingHom.algebraMap_toAlgebra]
      · simp only [Scheme.affineBasicOpen_coe, RingHom.mem_ker] at hx
        rw [← IsLocalization.mk'_spec' (M := .powers s), map_mul, hx, mul_zero]
    rwa [f.naturality] at hx

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.le_ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y.Hom Z),   g.ker ≤ 
AlgebraicGeometry.Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp f g)
参数：f : X ⟶ Y；g : Y.Hom Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals_mono`：ofIdeals_mono : M
onotone (ofIdeals (X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `Ideal.ker_le_comap`：ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <
= comap f K
-/
lemma Hom.le_ker_comp (f : X ⟶ Y) (g : Y.Hom Z) : g.ker ≤ (f ≫ g).ker := by
  refine ofIdeals_mono fun U ↦ ?_
  rw [Scheme.Hom.comp_app f g U, CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact Ideal.ker_le_comap _
/-
**AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：ker_eq_top_of_isEmpty (f : X.Hom Y) [IsEmpty X] : f.ker = ⊤
参数：f : X.Hom Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff`：le_ofIdeals_iff
 {I : IdealSheafData X} {J} : I <= ofIdeals J ↔ I.ideal <= J
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `AlgebraicGeometry.instSubsingletonCarrierObjOppositeOpensCarrierCarrierC
ommRingCatPresheafOpOpensOfIsEmpty`：∀ {X : AlgebraicGeometry.Scheme} [IsEmpty ↥X
] (U : X.Opens), Subsingleton ↑(X.presheaf.obj (Opposite.op U))
-/
lemma ker_eq_top_of_isEmpty (f : X.Hom Y) [IsEmpty X] : f.ker = ⊤ :=
  top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ ↦ by simpa using Subsingleton.elim _ _)

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.ker_eq_bot_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], A
lgebraicGeometry.Scheme.Hom.ker f = ⊥
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `AlgebraicGeometry.quasiCompact_of_isIso`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.QuasiCompact f
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Hom.ker_eq_bot_of_isIso (f : X ⟶ Y) [IsIso f] : f.ker = ⊥ := by
  ext U
  simp [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f.app U)).1]
/-
**AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [CategoryTheo
ry.IsIso f],   AlgebraicGeometry.Scheme.Hom.ker (CategoryTheory.CategoryStruct.c
omp f g) = AlgebraicGeometry.Scheme.Hom.ker g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `AlgebraicGeometry.Scheme.Hom.le_ker_comp`：∀ {X Y Z : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (g : Y.Hom Z),   g.ker ≤ AlgebraicGeometry.Scheme.Hom.ker (Ca
tegoryTheory.CategoryStruct.co…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
-/
lemma Hom.ker_comp_of_isIso (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : (f ≫ g).ker = g.ker :=
  (f.le_ker_comp g).antisymm' (((inv f).le_ker_comp _).trans (by simp))

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.ker_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：ker_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] : f.ker = ofIdealT
op (RingHom.ker f.appTop.hom)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_of_isAffine`：le_of_isAffine [
IsAffine X] {I J : IdealSheafData X} (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ <= J.i
deal ⟨⊤, isAffineOpen_top X⟩) : I <= J
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ideal_ker_le`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X.Hom Y) (U : ↑Y.affineOpens),   f.ker.ideal U ≤ RingHom.ker (CommRin
gCat.Hom.hom (f.app ↑U))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal`：∀ {X : Algebra
icGeometry.Scheme} (I : Ideal ↑(X.presheaf.obj (Opposite.op ⊤))) (U : ↑X.affineO
pens),   (AlgebraicGeometry.Scheme.IdealSheafD…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `Ideal.map_id`：map_id : I.map (RingHom.id R) = I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff`：le_ofIdeals_iff
 {I : IdealSheafData X} {J} : I <= ofIdeals J ↔ I.ideal <= J
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `RingHom.ker.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomCl
ass F R S] (…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.naturality`：naturality (i : op U' ⟶ op U) :
 Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map 
i.unop).op
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma ker_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    f.ker = ofIdealTop (RingHom.ker f.appTop.hom) := by
  refine (le_of_isAffine ((f.ideal_ker_le _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U ↦ ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual
/-
**AlgebraicGeometry.Scheme.Hom.range_subset_ker_support** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), Set.range ⇑f ⊆ ↑(Algebraic
Geometry.Scheme.Hom.ker f).support
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.ker f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter`：coe_support_i
nter (I : IdealSheafData X) (U : X.affineOpens) : (I.support : Set X) inter U = 
X.zeroLocus (U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_zero`：basicOpen_zero (U : X.Opens) : 
X.basicOpen (0 : Γ(X, U)) = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ideal_ker_le`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X.Hom Y) (U : ↑Y.affineOpens),   f.ker.ideal U ≤ RingHom.ker (CommRin
gCat.Hom.hom (f.app ↑U))
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
-/
lemma Hom.range_subset_ker_support (f : X ⟶ Y) :
    Set.range f ⊆ f.ker.support := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ((coe_support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x ∈ f ⁻¹ᵁ Y.basicOpen s := hxs
  rwa [Scheme.preimage_basicOpen, RingHom.mem_ker.mp (f.ideal_ker_le _ hs),
    Scheme.basicOpen_zero] at this
/-
**AlgebraicGeometry.Scheme.Hom.ker_eq_top_iff_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.Hom Y), f.ker = ⊤ ↔ IsEmpty ↥X
参数：f : X.Hom Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_subset_ker_support`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y), Set.range ⇑f ⊆ ↑(AlgebraicGeometry.Scheme.Hom.ker
 f).support
· 使用引理 `AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty`：ker_eq_top_of_isEmpty (f
 : X.Hom Y) [IsEmpty X] : f.ker = ⊤
-/
lemma Hom.ker_eq_top_iff_isEmpty (f : X.Hom Y) : f.ker = ⊤ ↔ IsEmpty X :=
  ⟨fun H ↦ by simpa [H] using f.range_subset_ker_support, fun _ ↦ ker_eq_top_of_isEmpty f⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.iInf_ker_openCover_map_comp_apply** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.Hom Y) [AlgebraicGeometry.QuasiC
ompact f] (𝒰 : X.OpenCover)   (U : ↑Y.affineOpens),   ⨅ i, (AlgebraicGeometry.Sc
heme.Hom.ker (CategoryTheory.CategoryStruct.comp (𝒰.f i) f)).ideal U = f.ker.ide
al U
参数：f : X.Hom Y；𝒰 : X.OpenCover；U : ↑Y.affineOpens；AlgebraicGeometry.Scheme.Hom.k
er (CategoryTheory.CategoryStruct.comp (𝒰.f i) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `TopCat.Presheaf.IsSheaf.section_ext`：∀ {X : TopCat} {A : Type u_1} [inst
 : CategoryTheory.Category.{u, u_1} A] {FC : A → A → Type u_2} {CC : A → Type u}
   [inst_1 : (X Y : A) → …
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsSheaf`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] (self : AlgebraicGeometry.SheafedSpace C),   self.presh
eaf.IsSheaf
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.coe_toRingHom`：coe_toRingHom (f : R ≃+* S) : ⇑(f : R ->+* S) =
 f
· 使用定理 `CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom`：∀ {R S : CommRin
gCat} (e : R ≅ S), ↑e.commRingCatIsoToRingEquiv = CommRingCat.Hom.hom e.hom
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom'`：appIso_hom' (U) : (f.appIso U)
.hom = f.appLE (f ''ᵁ U) U (preimage_image_eq f U).ge
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
（共 39 条，此处仅展示前 30 条）
-/
lemma Hom.iInf_ker_openCover_map_comp_apply
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) (U : Y.affineOpens) :
    ⨅ i, (𝒰.f i ≫ f).ker.ideal U = f.ker.ideal U := by
  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, map_zero, exists_and_left]
  refine ⟨𝒰.f i ''ᵁ 𝒰.f i ⁻¹ᵁ f ⁻¹ᵁ U.1, ⟨_, hxU, rfl⟩,
    Set.image_preimage_subset (𝒰.f i) (f ⁻¹ᵁ U), ?_⟩
  apply ((𝒰.f i).appIso _).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  simpa [Scheme.Hom.appLE] using! ideal_ker_le _ _ (Ideal.mem_iInf.mp hs i)
/-
**AlgebraicGeometry.Scheme.Hom.iInf_ker_openCover_map_comp** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f] (𝒰 : X.OpenCover),   ⨅ i, AlgebraicGeometry.Scheme.Hom.ker (CategoryTheo
ry.CategoryStruct.comp (𝒰.f i) f) =     AlgebraicGeometry.Scheme.Hom.ker f
参数：f : X ⟶ Y；𝒰 : X.OpenCover；CategoryTheory.CategoryStruct.comp (𝒰.f i) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_le_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteSemilattice
Inf α] {a : α} {s : ι → α},   iInf s ≤ a ↔ ∀ (b : α), (∀ (i : ι), b ≤ s i) → b ≤
 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.iInf_ker_openCover_map_comp_apply`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (𝒰 :
 X.OpenCover)   (U : ↑Y.affineOpens),   ⨅ i, (Algebr…
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.le_ker_comp`：∀ {X Y Z : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (g : Y.Hom Z),   g.ker ≤ AlgebraicGeometry.Scheme.Hom.ker (Ca
tegoryTheory.CategoryStruct.co…
-/
lemma Hom.iInf_ker_openCover_map_comp (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover) :
    ⨅ i, (𝒰.f i ≫ f).ker = f.ker := by
  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f)
  refine iInf_le_iff.mpr fun I hI U ↦ ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰, le_iInf_iff]
  exact fun i ↦ hI i U
/-
**AlgebraicGeometry.Scheme.Hom.iUnion_support_ker_openCover_map_comp** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.Hom Y) [AlgebraicGeometry.QuasiC
ompact f] (𝒰 : X.OpenCover) [Finite 𝒰.I₀],   ⋃ i, ↑(AlgebraicGeometry.Scheme.Hom
.ker (CategoryTheory.CategoryStruct.comp (𝒰.f i) f)).support = ↑f.ker.support
参数：f : X.Hom Y；𝒰 : X.OpenCover；AlgebraicGeometry.Scheme.Hom.ker (CategoryTheory.
CategoryStruct.comp (𝒰.f i) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用引理 `AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty`：ker_eq_top_of_isEmpty (f
 : X.Hom Y) [IsEmpty X] : f.ker = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter`：coe_support_i
nter (I : IdealSheafData X) (U : X.affineOpens) : (I.support : Set X) inter U = 
X.zeroLocus (U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.iInf_ker_openCover_map_comp_apply`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (𝒰 :
 X.OpenCover)   (U : ↑Y.affineOpens),   ⨅ i, (Algebr…
· 使用定理 `AlgebraicGeometry.Scheme.zeroLocus_iInf_of_nonempty`：∀ {X : AlgebraicGeo
metry.Scheme} {U : X.Opens} {ι : Type u_1} (I : ι → Ideal ↑(X.presheaf.obj (Oppo
site.op U)))   [Finite ι] [Nonempty ι], X…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Hom.iUnion_support_ker_openCover_map_comp
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) [Finite 𝒰.I₀] :
    ⋃ i, ((𝒰.f i ≫ f).ker.support : Set Y) = f.ker.support := by
  cases isEmpty_or_nonempty 𝒰.I₀
  · have : IsEmpty X := Function.isEmpty 𝒰.idx
    simp [ker_eq_top_of_isEmpty]
  suffices ∀ U : Y.affineOpens,
      (⋃ i, (𝒰.f i ≫ f).ker.support) ∩ U = (f.ker.support ∩ U : Set Y) by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    simpa [hxU] using congr(x ∈ $(this ⟨U, hU⟩))
  intro U
  simp only [Set.iUnion_inter, coe_support_inter, ← f.iInf_ker_openCover_map_comp_apply 𝒰,
    Scheme.zeroLocus_iInf_of_nonempty]
/-
**AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：ker_morphismRestrict_ideal (f : X.Hom Y) [QuasiCompact f] (U : Y.Opens) (V
 : U.toScheme.affineOpens) : (f ∣_ U).ker.ideal V = f.ker.ideal ⟨U.ι ''ᵁ V, V.2.
image_of_isOpenImmersion _⟩
参数：f : X.Hom Y；U : Y.Opens；V : U.toScheme.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `AlgebraicGeometry.instQuasiCompactMorphismRestrict`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) (V : Y.Opens) [AlgebraicGeometry.QuasiCompact f],   A
lgebraicGeometry.QuasiCompact (f ∣_ V)
· 使用定理 `RingHom.ker.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomCl
ass F R S] (…
· 使用定理 `AlgebraicGeometry.morphismRestrict_app'`：morphismRestrict_app' {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ∣_ U).app V = f.appLE _ _
 (image_morphismRestrict_prei…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
-/
lemma ker_morphismRestrict_ideal (f : X.Hom Y) [QuasiCompact f]
    (U : Y.Opens) (V : U.toScheme.affineOpens) :
    (f ∣_ U).ker.ideal V = f.ker.ideal ⟨U.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩ := by
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).1
/-
**AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：ker_ideal_of_isPullback_of_isOpenImmersion {X Y U V : Scheme.{u}} (f : X ⟶
 Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV] [QuasiCompact f]
 (H : IsPullback f' iU iV f) (W) : f'.ker.ideal W = (f.ker.ideal ⟨iV ''ᵁ W, W.2.
image_of_isOpenImmersion _⟩).comap (iV.appIso W).inv.hom
参数：f : X ⟶ Y；f' : U ⟶ V；iU : U ⟶ X；iV : V ⟶ Y；H : IsPullback f' iU iV f；W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_is
Pullback`：image_preimage_eq_preimage_image_of_isPullback {X Y U V : Scheme.{u}} 
{f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom'`：appIso_hom' (U) : (f.appIso U)
.hom = f.appLE (f ''ᵁ U) U (preimage_image_eq f U).ge
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.congr_simp`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) (U : Y.Opens) (V : X.Opens)   (e : V ≤
 (TopologicalSpace.Opens.map f.base…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 39 条，此处仅展示前 30 条）
-/
lemma ker_ideal_of_isPullback_of_isOpenImmersion {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV]
    [QuasiCompact f] (H : IsPullback f' iU iV f) (W) :
    f'.ker.ideal W =
      (f.ker.ideal ⟨iV ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).comap (iV.appIso W).inv.hom := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback H inferInstance
  ext x
  have : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
  let e : Γ(X, f ⁻¹ᵁ iV ''ᵁ W) ≅ Γ(U, f' ⁻¹ᵁ W) :=
    X.presheaf.mapIso (eqToIso this).op ≪≫ iU.appIso _
  have : (iV.appIso W).inv ≫ f.app _ = f'.app W ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, e, Scheme.Hom.appLE_comp_appLE, H.w]
  simp only [Scheme.Hom.ker_apply, RingHom.mem_ker, Ideal.mem_comap, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, this]
  simpa using (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv).1).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.support_ker** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f],   ↑(AlgebraicGeometry.Scheme.Hom.ker f).support = closure (Set.range ⇑f
)
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.ker f；Set.range ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ker_of_isAffine`：ker_of_isAffine {X Y : Scheme}
 (f : X ⟶ Y) [IsAffine Y] : f.ker = ofIdealTop (RingHom.ker f.appTop.hom)
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_ofIdealTop`：∀ {X : A
lgebraicGeometry.Scheme} (I : Ideal ↑(X.presheaf.obj (Opposite.op ⊤))),   ↑(Alge
braicGeometry.Scheme.IdealSheafData.ofIdealTop I).su…
· 使用定理 `AlgebraicGeometry.Spec_zeroLocus`：Spec_zeroLocus {R : CommRingCat} (s : 
Set Γ(Spec R, ⊤)) : (Spec R).zeroLocus s = PrimeSpectrum.zeroLocus ((Scheme.ΓSpe
cIso R).inv ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.coe_comap`：coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f
 I : Set R) = f ⁻¹' I
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用引理 `PrimeSpectrum.closure_range_comap`：closure_range_comap : closure (Set.ra
nge (comap f)) = zeroLocus (RingHom.ker f)
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`：ΓSpecIso_inv_naturalit
y {R S : CommRingCat.{u}} (f : R ⟶ S) : f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv 
≫ (Spec.map f).appTop
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.iUnion_support_ker_openCover_map_comp`：∀ {X
 Y : AlgebraicGeometry.Scheme} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] 
(𝒰 : X.OpenCover) [Finite 𝒰.I₀],   ⋃ i, ↑(AlgebraicGeome…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
（共 66 条，此处仅展示前 30 条）
-/
lemma Hom.support_ker (f : X ⟶ Y) [QuasiCompact f] :
    f.ker.support = closure (Set.range f) := by
  apply subset_antisymm
  · wlog hY : ∃ S, Y = Spec S
    · intro x hx
      let 𝒰 := Y.affineCover
      obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
      have inst : QuasiCompact (𝒰.pullbackHom f i) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      have := this (𝒰.pullbackHom f i) ⟨_, rfl⟩
        ((coe_support_inter _ ⟨⊤, isAffineOpen_top _⟩).ge ⟨?_, Set.mem_univ x⟩).1
      · have := image_closure_subset_closure_image (f := 𝒰.f i)
          (𝒰.f i).continuous (Set.mem_image_of_mem _ this)
        rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, 𝒰.pullbackHom_map] at this
        exact closure_mono (Set.range_comp_subset_range _ _) this
      · rw [← (𝒰.f i).isOpenEmbedding.injective.mem_set_image, Scheme.image_zeroLocus,
          ker_ideal_of_isPullback_of_isOpenImmersion f (𝒰.pullbackHom f i)
            ((𝒰.pullback₁ f).f i) (𝒰.f i),
          Ideal.coe_comap, Set.image_preimage_eq]
        · exact ⟨((coe_support_inter _ _).le ⟨hx, by simp⟩).1, ⟨_, rfl⟩⟩
        · exact (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso ⊤).inv).2
        · exact (IsPullback.of_hasPullback _ _).flip
    obtain ⟨S, rfl⟩ := hY
    wlog hX : ∃ R, X = Spec R generalizing X S
    · intro x hx
      have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
      let 𝒰 := X.affineCover.finiteSubcover
      obtain ⟨_, ⟨i, rfl⟩, hx⟩ := (f.iUnion_support_ker_openCover_map_comp 𝒰).ge hx
      have inst : QuasiCompact (𝒰.f i ≫ f) := HasAffineProperty.iff_of_isAffine.mpr
        (inferInstanceAs <| CompactSpace (Spec _))
      exact closure_mono (Set.range_comp_subset_range _ _) (this S (𝒰.f i ≫ f) ⟨_, rfl⟩ hx)
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    rw [ker_of_isAffine, coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap,
      RingHom.comap_ker, ← PrimeSpectrum.closure_range_comap, ← CommRingCat.hom_comp,
      ← Scheme.ΓSpecIso_inv_naturality]
    simp only [CommRingCat.hom_comp, PrimeSpectrum.comap_comp]
    exact closure_mono (Set.range_comp_subset_range _ (Spec.map φ))
  · rw [(support _).isClosed.closure_subset_iff]
    exact f.range_subset_ker_support

/-- The functor taking a morphism into `Y` to its kernel as an ideal sheaf on `Y`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.kerFunctor** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：kerFunctor (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ IdealSheafData Y where obj f
参数：Y : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a morphism into `Y` to its kernel as an ideal sheaf on `Y`.
-/
def kerFunctor (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ IdealSheafData Y where
  obj f := f.unop.hom.ker
  map {f g} hfg := homOfLE <| by simpa only [Functor.id_obj, Functor.const_obj_obj,
    OrderDual.toDual_le_toDual, ← Over.w hfg.unop] using hfg.unop.left.le_ker_comp f.unop.hom
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable (X) in
@[simp]
/-
**AlgebraicGeometry.Scheme.ker_toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_toSpecΓ [CompactSpace X] : X.toSpecΓ.ker = ⊥ := by
  apply IdealSheafData.ext_of_isAffine
  simpa using! RingHom.ker_coe_equiv (ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv

end ker

end Scheme

end AlgebraicGeometry

