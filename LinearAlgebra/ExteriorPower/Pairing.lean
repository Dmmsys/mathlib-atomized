/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Pairing

/-!
# The pairing between the exterior power of the dual and the exterior power

We construct the pairing
`exteriorPower.pairingDual : ⋀[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⋀[R]^n M))`.

-/

@[expose] public section

namespace exteriorPower

open TensorProduct PiTensorProduct

variable (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear map from the `n`th exterior power to the `n`th tensor power obtained by
`MultilinearMap.alternatization`. -/
/-
**exteriorPower.toTensorPower** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：toTensorPower (n : Nat) : ⋀[R]^n M ->ₗ[R] ⨂[R]^n M
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from the `n`th exterior power to the `n`th tensor power obtained 
by
`MultilinearMap.alternatization`.
-/
noncomputable def toTensorPower (n : ℕ) : ⋀[R]^n M →ₗ[R] ⨂[R]^n M :=
  alternatingMapLinearEquiv (MultilinearMap.alternatization (PiTensorProduct.tprod R))

variable {M} in
open Equiv in
@[simp]
/-
**exteriorPower.toTensorPower_apply_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toTensorPower_apply_ιMulti {n : ℕ} (v : Fin n → M) :
    toTensorPower R M n (ιMulti R n v) =
      ∑ σ : Perm (Fin n), Perm.sign σ • PiTensorProduct.tprod R (fun i ↦ v (σ i)) := by
  dsimp [toTensorPower]
  simp only [alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

/-- The canonical `n`-alternating map from the dual of the `R`-module `M`
to the dual of `⋀[R]^n M`. -/
/-
**exteriorPower.alternatingMapToDual** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：alternatingMapToDual (n : Nat) : AlternatingMap R (Module.Dual R M) (Modul
e.Dual R (⋀[R]^n M)) (Fin n) where toMultilinearMap
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `n`-alternating map from the dual of the `R`-module `M`
to the dual of `⋀[R]^n M`.
-/
noncomputable def alternatingMapToDual (n : ℕ) :
    AlternatingMap R (Module.Dual R M) (Module.Dual R (⋀[R]^n M)) (Fin n) where
  toMultilinearMap := (toTensorPower R M n).dualMap.compMultilinearMap
    (TensorPower.multilinearMapToDual R M n)
  map_eq_zero_of_eq' f i j hf hij := by
    ext v
    suffices Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) = 0 by
      simpa [Matrix.det_apply] using this
    exact Matrix.det_zero_of_column_eq hij (by simp [hf])

variable {R M} in
open Equiv in
@[simp]
/-
**exteriorPower.alternatingMapToDual_apply_** 是 Mathlib 中的一个定理，位于命名空间 `exteriorP
ower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingMapToDual_apply_ιMulti {n : ℕ}
    (f : (_ : Fin n) → Module.Dual R M) (v : Fin n → M) :
    alternatingMapToDual R M n f (ιMulti _ _ v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) := by
  simp [alternatingMapToDual, Matrix.det_apply]

/-- The linear map from the exterior power of the dual to the dual of the exterior power. -/
/-
**exteriorPower.pairingDual** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：pairingDual (n : Nat) : ⋀[R]^n (Module.Dual R M) ->ₗ[R] Module.Dual R (⋀[R
]^n M)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from the exterior power of the dual to the dual of the exterior p
ower.
-/
noncomputable def pairingDual (n : ℕ) :
    ⋀[R]^n (Module.Dual R M) →ₗ[R] Module.Dual R (⋀[R]^n M) :=
  alternatingMapLinearEquiv (alternatingMapToDual R M n)

variable {R M} in
open Equiv in
@[simp]
/-
**exteriorPower.pairingDual_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pairingDual_ιMulti_ιMulti {n : ℕ} (f : (_ : Fin n) → Module.Dual R M) (v : Fin n → M) :
    pairingDual R M n (ιMulti _ _ f) (ιMulti _ _ v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) := by
  simp [pairingDual]


section

/-! If an `R`-module `M` has a family of vectors `x : ι → M` and linear maps `f : ι → M`
such that `f i (x j)` is `1` or `0` depending on `i = j` or `i ≠ j`, then if `ι` has
a linear order, then a similar property regarding `pairingDual R M n`
applies to the family of vectors indexed
by `Fin n ↪o ι` in `⋀[R]^n M` and in `⋀[R]^n (Module.Dual R M)` that are obtained
by taking exterior products of the `x i` and the `f j`. (This shall be used in order
to construct a basis of `⋀[R]^n M` when `M` is a free module.) -/

variable {R M} {ι : Type*} [LinearOrder ι]
  (x : ι → M) (f : ι → Module.Dual R M)
  (h₁ : ∀ i, f i (x i) = 1) (h₀ : ∀ ⦃i j⦄, i ≠ j → f i (x j) = 0) (n : ℕ)

include h₁ h₀ in
/-
**exteriorPower.pairingDual_apply_apply_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `exteri
orPower`。
形式化陈述：pairingDual_apply_apply_eq_one (a : Fin n ↪o ι) : pairingDual R M n (ιMult
i _ _ (f ∘ a)) (ιMulti _ _ (x ∘ a)) = 1
参数：a : Fin n ↪o ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `exteriorPower.pairingDual_ιMulti_ιMulti`：pairingDual_ιMulti_ιMulti {n : 
Nat} (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) : pairingDual R M n (
ιMulti _ _ f) (ιMulti _ _ v) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RelEmbedding.instEmbeddingLike`：∀ {α : Type u_1} {β : Type u_2} {r : α →
 α → Prop} {s : β → β → Prop}, EmbeddingLike (r ↪r s) α β
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
-/
lemma pairingDual_apply_apply_eq_one (a : Fin n ↪o ι) :
    pairingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ a)) = 1 := by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply]
  rw [← Matrix.det_one (n := Fin n)]
  congr
  ext i j
  dsimp
  by_cases hij : i = j
  · subst hij
    simp only [h₁, Matrix.one_apply_eq]
  · rw [h₀ (by simpa using Ne.symm hij), Matrix.one_apply_ne hij]

include h₀ in
/-
**exteriorPower.pairingDual_apply_apply_eq_one_zero** 是 Mathlib 中的一个引理，位于命名空间 `e
xteriorPower`。
形式化陈述：pairingDual_apply_apply_eq_one_zero (a b : Fin n ↪o ι) (h : a != b) : pair
ingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ b)) = 0
参数：a b : Fin n ↪o ι；h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `exteriorPower.pairingDual_ιMulti_ιMulti`：pairingDual_ιMulti_ιMulti {n : 
Nat} (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) : pairingDual R M n (
ιMulti _ _ f) (ιMulti _ _ v) …
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
（共 31 条，此处仅展示前 30 条）
-/
lemma pairingDual_apply_apply_eq_one_zero (a b : Fin n ↪o ι) (h : a ≠ b) :
    pairingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ b)) = 0 := by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply, Matrix.det_apply]
  refine Finset.sum_eq_zero (fun σ _ ↦ ?_)
  simp only [Matrix.of_apply, smul_eq_iff_eq_inv_smul, smul_zero]
  by_contra h'
  apply h
  have : a = b ∘ σ := by
    ext i
    by_contra hi
    exact h' (Finset.prod_eq_zero (i := i) (by simp) (h₀ hi))
  have hσ : Monotone σ := fun i j hij ↦ by
    have h'' := congr_fun this
    dsimp at h''
    rw [← a.map_rel_iff] at hij
    simpa only [← b.map_rel_iff, ← h'']
  have hσ' : Monotone σ.symm := fun i j hij ↦ by
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    simp only [Equiv.symm_apply_apply]
    by_contra! h
    obtain rfl : i = j := σ.injective (le_antisymm hij (hσ h.le))
    simp only [lt_self_iff_false] at h
  obtain rfl : σ = 1 := by
    ext i : 1
    exact DFunLike.congr_fun (Subsingleton.elim (σ.toOrderIso hσ hσ') (OrderIso.refl _)) i
  ext
  apply congr_fun this

end

end exteriorPower

