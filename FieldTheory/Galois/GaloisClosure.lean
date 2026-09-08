/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!

# Main definitions and results

In a field extension `K/k`

* `FiniteGaloisIntermediateField` : The type of intermediate fields of `K/k`
  that are finite and Galois over `k`

* `adjoin` : The finite Galois intermediate field obtained from the normal closure of adjoining a
  finite `s : Set K` to `k`.

## TODO

* `FiniteGaloisIntermediateField` should be a `ConditionallyCompleteLattice` but isn't proved yet.

-/

@[expose] public section

open IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The type of intermediate fields of `K/k` that are finite and Galois over `k` -/
/-
**FiniteGaloisIntermediateField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u_1) → (K : Type u_2) → [inst : Field k] → [inst_1 : Field K] → 
[Algebra k K] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of intermediate fields of `K/k` that are finite and Galois over `k`
-/
structure FiniteGaloisIntermediateField extends IntermediateField k K where
  [finiteDimensional : FiniteDimensional k toIntermediateField]
  [isGalois : IsGalois k toIntermediateField]

namespace FiniteGaloisIntermediateField

/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K) where
  coe := toIntermediateField
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (FiniteGaloisIntermediateField k K) (Type _) where
  coe L := L.toIntermediateField
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L :=
  L.finiteDimensional
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L := L.isGalois

variable {k K}
/-
**FiniteGaloisIntermediateField.val_injective** 是 Mathlib 中的一个引理，位于命名空间 `FiniteG
aloisIntermediateField`。
形式化陈述：val_injective : Function.Injective (toIntermediateField (k
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteGaloisIntermediateField.mk.injEq`：∀ {k : Type u_1} {K : Type u_2} 
[inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K]   (toIntermediateFiel
d : IntermediateField k K) […
-/
lemma val_injective : Function.Injective (toIntermediateField (k := k) (K := K)) := by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

/-- Turns the collection of finite Galois IntermediateFields of `K/k` into a lattice. -/
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns the collection of finite Galois IntermediateFields of `K/k` into a lattice
.
-/
instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊔ L₂) where
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₁] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₁) inf_le_left).toLinearMap
    (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₁) inf_le_left).toRingHom.injective
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₂] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₂) inf_le_right).toLinearMap
    (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₂) inf_le_right).injective
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₁] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_left)
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₂] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_right)
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊓ L₂) where
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (FiniteGaloisIntermediateField k K) where
  max L₁ L₂ := .mk <| L₁ ⊔ L₂
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (FiniteGaloisIntermediateField k K) where
  min L₁ L₂ := .mk <| L₁ ⊓ L₂
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (FiniteGaloisIntermediateField k K) :=
  PartialOrder.lift _ val_injective
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (FiniteGaloisIntermediateField k K) :=
  val_injective.lattice _ .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**FiniteGaloisIntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGaloisIntermed
iateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (FiniteGaloisIntermediateField k K) where
  bot := .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

@[simp]
/-
**FiniteGaloisIntermediateField.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `FiniteGaloisIn
termediateField`。
形式化陈述：le_iff (L₁ L₂ : FiniteGaloisIntermediateField k K) : L₁ <= L₂ ↔ L₁.toInter
mediateField <= L₂.toIntermediateField
参数：L₁ L₂ : FiniteGaloisIntermediateField k K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff (L₁ L₂ : FiniteGaloisIntermediateField k K) :
    L₁ ≤ L₂ ↔ L₁.toIntermediateField ≤ L₂.toIntermediateField :=
  Iff.rfl

variable (k) in
/-- The minimal (finite) Galois intermediate field containing a finite set `s : Set K` in a
Galois extension `K/k` defined as the normal closure of the field obtained by adjoining
the set `s : Set K` to `k`. -/
/-
**FiniteGaloisIntermediateField.adjoin** 是 Mathlib 中的一个定义，位于命名空间 `FiniteGaloisIn
termediateField`。
形式化陈述：adjoin [IsGalois k K] (s : Set K) [Finite s] : FiniteGaloisIntermediateFie
ld k K
参数：s : Set K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal (finite) Galois intermediate field containing a finite set `s : Set 
K` in a
Galois extension `K/k` defined as the normal closure of the field obtained by ad
joining
the set `s : Set K` to `k`.
-/
noncomputable def adjoin [IsGalois k K] (s : Set K) [Finite s] :
    FiniteGaloisIntermediateField k K := {
  normalClosure k (IntermediateField.adjoin k (s : Set K)) K with
  finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) :=
      IntermediateField.finiteDimensional_adjoin <| fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    normalClosure.is_finiteDimensional k (IntermediateField.adjoin k (s : Set K)) K
  isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k (s : Set K)) K }

@[simp]
/-
**FiniteGaloisIntermediateField.adjoin_val** 是 Mathlib 中的一个引理，位于命名空间 `FiniteGalo
isIntermediateField`。
形式化陈述：adjoin_val [IsGalois k K] (s : Set K) [Finite s] : (FiniteGaloisIntermedia
teField.adjoin k s) = normalClosure k (IntermediateField.adjoin k s) K
参数：s : Set K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adjoin_val [IsGalois k K] (s : Set K) [Finite s] :
    (FiniteGaloisIntermediateField.adjoin k s) =
    normalClosure k (IntermediateField.adjoin k s) K :=
  rfl

variable (k) in
/-
**FiniteGaloisIntermediateField.subset_adjoin** 是 Mathlib 中的一个引理，位于命名空间 `FiniteG
aloisIntermediateField`。
形式化陈述：subset_adjoin [IsGalois k K] (s : Set K) [Finite s] : s subseteq (adjoin k
 s).toIntermediateField
参数：s : Set K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L
-/
lemma subset_adjoin [IsGalois k K] (s : Set K) [Finite s] :
    s ⊆ (adjoin k s).toIntermediateField :=
  (IntermediateField.subset_adjoin k s).trans (IntermediateField.le_normalClosure _)
/-
**FiniteGaloisIntermediateField.adjoin_simple_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `
FiniteGaloisIntermediateField`。
形式化陈述：adjoin_simple_le_iff [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateF
ield k K} : adjoin k {x} <= L ↔ x in L.toIntermediateField
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateField`：∀
 (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [inst_2 : Alg
ebra k K]   (L : FiniteGaloisIntermediateField k K), IsGalo…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adjoin_simple_le_iff [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} :
    adjoin k {x} ≤ L ↔ x ∈ L.toIntermediateField := by
  simp only [le_iff, adjoin_val, IntermediateField.normalClosure_le_iff_of_normal,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]

@[simp]
/-
**FiniteGaloisIntermediateField.adjoin_map** 是 Mathlib 中的一个定理，位于命名空间 `FiniteGalo
isIntermediateField`。
形式化陈述：adjoin_map [IsGalois k K] (f : K ->ₐ[k] K) (s : Set K) [Finite s] : adjoin
 k (f '' s) = adjoin k s
参数：f : K ->ₐ[k] K；s : Set K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FiniteGaloisIntermediateField.val_injective`：val_injective : Function.In
jective (toIntermediateField (k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_map`：adjoin_map {E' : Type*} [Field E'] [Algebr
a F E'] (f : E ->ₐ[F] E') : (adjoin F S).map f = adjoin F (f '' S)
· 使用引理 `IntermediateField.normalClosure_map_eq`：normalClosure_map_eq (K : Interm
ediateField F L) (σ : L ->ₐ[F] L) : normalClosure F (K.map σ) L = normalClosure 
F K L
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
-/
theorem adjoin_map [IsGalois k K] (f : K →ₐ[k] K) (s : Set K) [Finite s] :
    adjoin k (f '' s) = adjoin k s := by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map, IntermediateField.normalClosure_map_eq]

@[simp]
/-
**FiniteGaloisIntermediateField.adjoin_simple_map_algHom** 是 Mathlib 中的一个定理，位于命名
空间 `FiniteGaloisIntermediateField`。
形式化陈述：adjoin_simple_map_algHom [IsGalois k K] (f : K ->ₐ[k] K) (x : K) : adjoin 
k {f x} = adjoin k {x}
参数：f : K ->ₐ[k] K；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteGaloisIntermediateField.adjoin.congr_simp`：∀ (k : Type u_1) {K : T
ype u_2} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] [inst_3 : Is
Galois k K]   (s s_1 : Set K) (e_s : …
· 使用定理 `FiniteGaloisIntermediateField.adjoin_map`：adjoin_map [IsGalois k K] (f :
 K ->ₐ[k] K) (s : Set K) [Finite s] : adjoin k (f '' s) = adjoin k s
-/
theorem adjoin_simple_map_algHom [IsGalois k K] (f : K →ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} := by
  simpa only [Set.image_singleton] using adjoin_map f { x }

@[simp]
/-
**FiniteGaloisIntermediateField.adjoin_simple_map_algEquiv** 是 Mathlib 中的一个定理，位于
命名空间 `FiniteGaloisIntermediateField`。
形式化陈述：adjoin_simple_map_algEquiv [IsGalois k K] (f : Gal(K/k)) (x : K) : adjoin 
k {f x} = adjoin k {x}
参数：f : Gal(K/k)；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteGaloisIntermediateField.adjoin_simple_map_algHom`：adjoin_simple_ma
p_algHom [IsGalois k K] (f : K ->ₐ[k] K) (x : K) : adjoin k {f x} = adjoin k {x}
-/
theorem adjoin_simple_map_algEquiv [IsGalois k K] (f : Gal(K/k)) (x : K) :
    adjoin k {f x} = adjoin k {x} :=
  adjoin_simple_map_algHom (f : K →ₐ[k] K) x

nonrec lemma mem_fixingSubgroup_iff (α : Gal(K/k)) (L : FiniteGaloisIntermediateField k K) :
    α ∈ L.fixingSubgroup ↔ α.restrictNormalHom L = 1 := by
  simp [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff, AlgEquiv.ext_iff, Subtype.ext_iff,
    AlgEquiv.restrictNormalHom_apply]

end FiniteGaloisIntermediateField

