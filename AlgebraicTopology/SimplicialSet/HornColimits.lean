/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Horns as colimits

In this file, we express horns as colimits:
* horns in `Δ[2]` are pushouts of two copies of `Δ[1]`;
* horns in `Δ[n]` are multicoequalizers of copies of the standard
  simplex of dimension `n-1` (a dedicated API is provided for inner
  horns in `Δ[3]`).

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial Opposite Limits

namespace horn₂₀

/-
**SSet.horn₂₀.sq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₂₀`。
形式化陈述：sq : Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1}
) (stdSimplex.face {0, 2}) Λ[2, 0] where sup_eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用引理 `SSet.face_le_horn`：face_le_horn {n : Nat} (i j : Fin (n + 1)) (h : i != 
j) : stdSimplex.face.{u} {i}ᶜ <= horn n j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.stdSimplex.face_inter_face`：face_inter_face {n : Nat} (S₁ S₂ : Fins
et (Fin (n + 1))) : face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂)
· 使用定理 `Finset.inter_insert_of_mem`：inter_insert_of_mem {s₁ s₂ : Finset α} {a : 
α} (h : a in s₁) : s₁ inter insert a s₂ = insert a (s₁ inter s₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.inter_singleton_of_notMem`：inter_singleton_of_notMem {a : α} {s :
 Finset α} (h : a ∉ s) : s inter {a} = ∅
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
-/
lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1})
    (stdSimplex.face {0, 2}) Λ[2, 0] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ Λ[2, 0]` which avoids `2`. -/
/-
**SSet.horn₂₀.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₂₀`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[1] ⟶ Λ[2, 0]` which avoids `2`.
-/
abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 2 (by simp)

/-- The inclusion `Δ[1] ⟶ Λ[2, 0]` which avoids `1`. -/
/-
**SSet.horn₂₀.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₂₀`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[1] ⟶ Λ[2, 0]` which avoids `1`.
-/
abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 1 (by simp)
/-
**SSet.horn₂₀.isPushout** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₂₀`。
形式化陈述：isPushout : IsPushout (stdSimplex.{u}.δ (1 : Fin 2)) (stdSimplex.{u}.δ (1 
: Fin 2)) ι₀₁ ι₀₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso'`：of_iso' {Z X Y P : C} {f : Z ⟶ X} {g :
 Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) {Z' X' Y' P' : C
} {f' : Z' ⟶ X'} {g' :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Lattice.BicartSq.le₁₂`：le₁₂ : x₁ <= x₂
· 使用引理 `SSet.horn₂₀.sq`：sq : Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdS
implex.face {0, 1}) (stdSimplex.face {0, 2}) Λ[2, 0] where sup_eq
· 使用引理 `Lattice.BicartSq.le₁₃`：le₁₃ : x₁ <= x₃
· 使用引理 `Lattice.BicartSq.le₂₄`：le₂₄ : x₂ <= x₄
· 使用引理 `Lattice.BicartSq.le₃₄`：le₃₄ : x₃ <= x₄
· 使用定理 `SSet.Subcomplex.BicartSq.isPushout`：∀ {X : _root_.SSet} {A₁ A₂ A₃ A₄ : X
.Subcomplex} (sq : A₁.BicartSq A₂ A₃ A₄),   CategoryTheory.IsPushout (SSet.Subco
mplex.homOfLE ⋯) (SSet.S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (1 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₀

namespace horn₂₁

/-
**SSet.horn₂₁.sq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₂₁`。
形式化陈述：sq : Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1}
) (stdSimplex.face {1, 2}) Λ[2, 1] where sup_eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用引理 `SSet.face_le_horn`：face_le_horn {n : Nat} (i j : Fin (n + 1)) (h : i != 
j) : stdSimplex.face.{u} {i}ᶜ <= horn n j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.stdSimplex.face_inter_face`：face_inter_face {n : Nat} (S₁ S₂ : Fins
et (Fin (n + 1))) : face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂)
· 使用定理 `Finset.inter_insert_of_mem`：inter_insert_of_mem {s₁ s₂ : Finset α} {a : 
α} (h : a in s₁) : s₁ inter insert a s₂ = insert a (s₁ inter s₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Finset.inter_singleton_of_notMem`：inter_singleton_of_notMem {a : α} {s :
 Finset α} (h : a ∉ s) : s inter {a} = ∅
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
-/
lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1})
    (stdSimplex.face {1, 2}) Λ[2, 1] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ Λ[2, 1]` which avoids `2`. -/
/-
**SSet.horn₂₁.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₂₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[1] ⟶ Λ[2, 1]` which avoids `2`.
-/
abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 2 (by simp)

/-- The inclusion `Δ[1] ⟶ Λ[2, 1]` which avoids `0`. -/
/-
**SSet.horn₂₁.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₂₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[1] ⟶ Λ[2, 1]` which avoids `0`.
-/
abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 0 (by simp)
/-
**SSet.horn₂₁.isPushout** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₂₁`。
形式化陈述：isPushout : IsPushout (stdSimplex.{u}.δ (0 : Fin 2)) (stdSimplex.{u}.δ (1 
: Fin 2)) ι₀₁ ι₁₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso'`：of_iso' {Z X Y P : C} {f : Z ⟶ X} {g :
 Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) {Z' X' Y' P' : C
} {f' : Z' ⟶ X'} {g' :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Lattice.BicartSq.le₁₂`：le₁₂ : x₁ <= x₂
· 使用引理 `SSet.horn₂₁.sq`：sq : Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdS
implex.face {0, 1}) (stdSimplex.face {1, 2}) Λ[2, 1] where sup_eq
· 使用引理 `Lattice.BicartSq.le₁₃`：le₁₃ : x₁ <= x₃
· 使用引理 `Lattice.BicartSq.le₂₄`：le₂₄ : x₂ <= x₄
· 使用引理 `Lattice.BicartSq.le₃₄`：le₃₄ : x₃ <= x₄
· 使用定理 `SSet.Subcomplex.BicartSq.isPushout`：∀ {X : _root_.SSet} {A₁ A₂ A₃ A₄ : X
.Subcomplex} (sq : A₁.BicartSq A₂ A₃ A₄),   CategoryTheory.IsPushout (SSet.Subco
mplex.homOfLE ⋯) (SSet.S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₁

namespace horn₂₂

/-
**SSet.horn₂₂.sq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₂₂`。
形式化陈述：sq : Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2}
) (stdSimplex.face {1, 2}) Λ[2, 2] where sup_eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用引理 `SSet.face_le_horn`：face_le_horn {n : Nat} (i j : Fin (n + 1)) (h : i != 
j) : stdSimplex.face.{u} {i}ᶜ <= horn n j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.stdSimplex.face_inter_face`：face_inter_face {n : Nat} (S₁ S₂ : Fins
et (Fin (n + 1))) : face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂)
· 使用定理 `Finset.inter_insert_of_notMem`：inter_insert_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₁) : s₁ inter insert a s₂ = s₁ inter s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Finset.inter_singleton_of_mem`：inter_singleton_of_mem {a : α} {s : Finse
t α} (h : a in s) : s inter {a} = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2})
    (stdSimplex.face {1, 2}) Λ[2, 2] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ Λ[2, 2]` which avoids `1`. -/
/-
**SSet.horn₂₂.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₂₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[1] ⟶ Λ[2, 2]` which avoids `1`.
-/
abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 1 (by simp)

/-- The inclusion `Δ[1] ⟶ Λ[2, 2]` which avoids `0`. -/
/-
**SSet.horn₂₂.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₂₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[1] ⟶ Λ[2, 2]` which avoids `0`.
-/
abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 0 (by simp)
/-
**SSet.horn₂₂.isPushout** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₂₂`。
形式化陈述：isPushout : IsPushout (stdSimplex.{u}.δ (0 : Fin 2)) (stdSimplex.{u}.δ (0 
: Fin 2)) ι₀₂ ι₁₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso'`：of_iso' {Z X Y P : C} {f : Z ⟶ X} {g :
 Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) {Z' X' Y' P' : C
} {f' : Z' ⟶ X'} {g' :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Lattice.BicartSq.le₁₂`：le₁₂ : x₁ <= x₂
· 使用引理 `SSet.horn₂₂.sq`：sq : Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdS
implex.face {0, 2}) (stdSimplex.face {1, 2}) Λ[2, 2] where sup_eq
· 使用引理 `Lattice.BicartSq.le₁₃`：le₁₃ : x₁ <= x₃
· 使用引理 `Lattice.BicartSq.le₂₄`：le₂₄ : x₂ <= x₄
· 使用引理 `Lattice.BicartSq.le₃₄`：le₃₄ : x₃ <= x₄
· 使用定理 `SSet.Subcomplex.BicartSq.isPushout`：∀ {X : _root_.SSet} {A₁ A₂ A₃ A₄ : X
.Subcomplex} (sq : A₁.BicartSq A₂ A₃ A₄),   CategoryTheory.IsPushout (SSet.Subco
mplex.homOfLE ⋯) (SSet.S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (0 : Fin 2)) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₂

namespace horn

variable {n : ℕ}

/-- The multicoequalizer diagram which expresses `Λ[n, i]` as a gluing
of all `1`-codimensional faces of the standard simplex but one
along suitable `2`-codimensional faces. -/
/-
**SSet.horn.multicoequalizerDiagram** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
形式化陈述：multicoequalizerDiagram (i : Fin (n + 1)) : Subcomplex.MulticoequalizerDia
gram Λ[n, i] (ι
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用引理 `SSet.stdSimplex.face_inter_face`：face_inter_face {n : Nat} (S₁ S₂ : Fins
et (Fin (n + 1))) : face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.compl_insert`：compl_insert : (insert a s)ᶜ = sᶜ.erase a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The multicoequalizer diagram which expresses `Λ[n, i]` as a gluing
of all `1`-codimensional faces of the standard simplex but one
along suitable `2`-codimensional faces.
-/
lemma multicoequalizerDiagram (i : Fin (n + 1)) :
    Subcomplex.MulticoequalizerDiagram Λ[n, i]
      (ι := ({i}ᶜ : Set (Fin (n + 1)))) (fun j ↦ stdSimplex.face {j.1}ᶜ)
      (fun j k ↦ stdSimplex.face {j.1, k.1}ᶜ) where
  iSup_eq := by rw [horn_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- The horn is a multicoequalizer of all `1`-codimensional faces of the
standard simplex but one along suitable `2`-codimensional faces. -/
/-
**SSet.horn.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：isColimit (i : Fin (n + 1)) : IsColimit ((multicoequalizerDiagram i).multi
cofork.toLinearOrder.map Subcomplex.toSSetFunctor)
参数：i : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.multicoequalizerDiagram`：multicoequalizerDiagram (i : Fin (n +
 1)) : Subcomplex.MulticoequalizerDiagram Λ[n, i] (ι

--- 原说明 ---
The horn is a multicoequalizer of all `1`-codimensional faces of the
standard simplex but one along suitable `2`-codimensional faces.
-/
noncomputable def isColimit (i : Fin (n + 1)) :
    IsColimit ((multicoequalizerDiagram i).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram i).isColimit'

variable {X : SSet.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.horn.hom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
形式化陈述：hom_ext' {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSet) ⟶ X} (h : forall (j
 : Fin (n + 2)) (hj : j != i), horn.ι i j hj ≫ f = horn.ι i j hj ≫ g) : f = g
参数：n + 2；Λ[n + 1, i] : SSet；h : forall (j : Fin (n + 2)) (hj : j != i), horn.ι i
 j hj ≫ f = horn.ι i j hj ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicofork.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MultispanShape}
   {I : CategoryTheory.Limits.MultispanIn…
· 使用引理 `SSet.horn.multicoequalizerDiagram`：multicoequalizerDiagram (i : Fin (n +
 1)) : Subcomplex.MulticoequalizerDiagram Λ[n, i] (ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.horn.faceSingletonComplIso_inv_ι_assoc`：∀ {n : ℕ} (i j : Fin (n + 2
)) (hij : j ≠ i) {Z : _root_.SSet} (h : (SSet.horn (n + 1) i).toSSet ⟶ Z),   Cat
egoryTheory.CategoryStruct.comp (…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
-/
lemma hom_ext' {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSet) ⟶ X}
    (h : ∀ (j : Fin (n + 2)) (hj : j ≠ i), horn.ι i j hj ≫ f = horn.ι i j hj ≫ g) :
    f = g := by
  refine Multicofork.IsColimit.hom_ext (isColimit i) (fun ⟨j, hj⟩ ↦ ?_)
  simpa only [faceSingletonComplIso_inv_ι_assoc] using!
    (stdSimplex.faceSingletonComplIso j).inv ≫= h j hj

/-- Let `i : Fin (n + 2)`. This is the condition that a family of morphisms
`Δ[n] ⟶ X` for `j ≠ i` are the "faces" of a morphism  `Λ[n + 1, i] ⟶ X`. -/
/-
**SSet.horn.IsCompatible** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：{n : ℕ} →   {X : _root_.SSet} → {i : Fin (n + 2)} → ((j : Fin (n + 2)) → j
 ≠ i → (SSet.stdSimplex.obj { len := n } ⟶ X)) → Prop
参数：n + 2；(j : Fin (n + 2)) → j ≠ i → (SSet.stdSimplex.obj { len := n } ⟶ X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `i : Fin (n + 2)`. This is the condition that a family of morphisms
`Δ[n] ⟶ X` for `j ≠ i` are the "faces" of a morphism  `Λ[n + 1, i] ⟶ X`.
-/
protected def IsCompatible
    {i : Fin (n + 2)} (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X) : Prop :=
  match n with
  | 0 => True
  | n + 1 => ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk

@[simp]
/-
**SSet.horn.isCompatible_zero_iff_true** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
形式化陈述：isCompatible_zero_iff_true {i : Fin 2} (f : forall (j : Fin 2) (_ : j != i
), Δ[0] ⟶ X) : horn.IsCompatible f ↔ True
参数：f : forall (j : Fin 2) (_ : j != i), Δ[0] ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCompatible_zero_iff_true {i : Fin 2} (f : ∀ (j : Fin 2) (_ : j ≠ i), Δ[0] ⟶ X) :
    horn.IsCompatible f ↔ True := Iff.rfl

@[simp]
/-
**SSet.horn.isCompatible_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
形式化陈述：isCompatible_iff {i : Fin (n + 3)} (f : forall (j : Fin (n + 3)) (_ : j !=
 i), Δ[n + 1] ⟶ X) : horn.IsCompatible f ↔ forall (j k : Fin (n + 3)) (hj : j !=
 i) (hk : k != i) (hjk : j < k), stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫
 f j hj = stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk
参数：n + 3；f : forall (j : Fin (n + 3)) (_ : j != i), Δ[n + 1] ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCompatible_iff
    {i : Fin (n + 3)} (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), Δ[n + 1] ⟶ X) :
    horn.IsCompatible f ↔
    ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk := Iff.rfl

namespace IsCompatible

/-
**SSet.horn.IsCompatible.of_hom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsCompatibl
e`。
形式化陈述：of_hom {i : Fin (n + 2)} (g : (Λ[n + 1, i] : SSet) ⟶ X) : horn.IsCompatibl
e (fun j hj => horn.ι i j hj ≫ g)
参数：n + 2；g : (Λ[n + 1, i] : SSet) ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.eq_castSucc_of_ne_last`：eq_castSucc_of_ne_last {x : Fin (n + 1)} (h 
: x != (last _)) : exists y, Fin.castSucc y = x
· 使用定理 `Fin.eq_succ_of_ne_zero`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ 0 → ∃ j, i = j.
succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `SSet.horn.ι_ι`：ι_ι {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : 
j != i) : ι i j hij ≫ Λ[n + 1, i].ι = stdSimplex.{u}.δ j
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
· 使用定理 `CategoryTheory.CosimplicialObject.δ_comp_δ`：δ_comp_δ {n} {i j : Fin (n +
 2)} (H : i <= j) : X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i)
-/
lemma of_hom {i : Fin (n + 2)} (g : (Λ[n + 1, i] : SSet) ⟶ X) :
    horn.IsCompatible (fun j hj ↦ horn.ι i j hj ≫ g) := by
  obtain _ | n := n
  · simp
  · simp only [isCompatible_iff, ← Category.assoc]
    intro j k hj hk hjk
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Category.assoc, ι_ι, ι_ι,
      Fin.pred_succ, Fin.castPred_castSucc, stdSimplex.δ_comp_δ (by grind)]

@[reassoc]
/-
**SSet.horn.IsCompatible.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsCompatible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_pred_comp {i : Fin (n + 3)} {f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet) ⟶ X}
    (hf : horn.IsCompatible f) (j k : Fin (n + 3))
    (hj : j ≠ i := by grind) (hk : k ≠ i := by grind) (hjk : j < k := by grind) :
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk :=
  hf j k hj hk hjk

variable {i : Fin (n + 2)} {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet) ⟶ X}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open stdSimplex in
/-- Auxiliary definition for `horn.IsCompatible.desc`. -/
/-
**SSet.horn.IsCompatible.multicofork** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn.IsComp
atible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `horn.IsCompatible.desc`.
-/
private def multicofork (hf : horn.IsCompatible f) :
    Multicofork ((multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
      (Subcomplex.toSSetFunctor)) :=
  Multicofork.ofπ _ X (fun ⟨j, hj⟩ ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ f j hj) (by
    obtain _ | n := n
    · rintro ⟨⟨a, b⟩, hab⟩
      grind
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab : a < b⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      dsimp
      rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc _ _ hab,
        homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc _ _ hab,
        hf.δ_pred_comp ..])

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.horn.IsCompatible.exists_desc** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsComp
atible`。
形式化陈述：exists_desc (hf : horn.IsCompatible f) : exists (φ : (Λ[n + 1, i] : SSet) 
⟶ X), forall (j : Fin (n + 2)) (hj : j != i), horn.ι i j hj ≫ φ = f j hj
参数：hf : horn.IsCompatible f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.multicoequalizerDiagram`：multicoequalizerDiagram (i : Fin (n +
 1)) : Subcomplex.MulticoequalizerDiagram Λ[n, i] (ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.horn.faceSingletonComplIso_inv_ι_assoc`：∀ {n : ℕ} (i j : Fin (n + 2
)) (hij : j ≠ i) {Z : _root_.SSet} (h : (SSet.horn (n + 1) i).toSSet ⟶ Z),   Cat
egoryTheory.CategoryStruct.comp (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Multicofork.map_ι_app`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] {J : Categor…
· 使用定理 `SSet.Subcomplex.toSSetFunctor_map`：∀ {X : _root_.SSet} {X_1 Y : X.Subcom
plex} (h : X_1 ⟶ Y),   SSet.Subcomplex.toSSetFunctor.map h = SSet.Subcomplex.hom
OfLE ⋯
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma exists_desc (hf : horn.IsCompatible f) :
    ∃ (φ : (Λ[n + 1, i] : SSet) ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), horn.ι i j hj ≫ φ = f j hj :=
  ⟨(horn.isColimit.{u} i).desc hf.multicofork, fun j hj ↦ by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv]
    simpa using! (horn.isColimit.{u} i).fac hf.multicofork (.right ⟨j, hj⟩)⟩

/-- Let `i : Fin (n + 2)`. Given a compatible family of morphisms `Δ[n] ⟶ X` for `j ≠ i`,
this is the glued morphism `Λ[n + 1, i] ⟶ X`. -/
@[no_expose]
/-
**SSet.horn.IsCompatible.desc** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn.IsCompatible`
。
形式化陈述：desc (hf : horn.IsCompatible f) : (Λ[n + 1, i] : SSet) ⟶ X
参数：hf : horn.IsCompatible f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.IsCompatible.exists_desc`：exists_desc (hf : horn.IsCompatible 
f) : exists (φ : (Λ[n + 1, i] : SSet) ⟶ X), forall (j : Fin (n + 2)) (hj : j != 
i), horn.ι i j hj ≫ φ = …

--- 原说明 ---
Let `i : Fin (n + 2)`. Given a compatible family of morphisms `Δ[n] ⟶ X` for `j 
≠ i`,
this is the glued morphism `Λ[n + 1, i] ⟶ X`.
-/
noncomputable def desc (hf : horn.IsCompatible f) : (Λ[n + 1, i] : SSet) ⟶ X :=
  hf.exists_desc.choose

@[reassoc (attr := simp)]
/-
**SSet.horn.IsCompatible.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsCompatible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_desc (hf : horn.IsCompatible f) (j : Fin (n + 2)) (hj : j ≠ i) :
    horn.ι i j hj ≫ hf.desc = f j hj :=
  hf.exists_desc.choose_spec j hj

end IsCompatible

end horn

namespace horn₃₁

/-- The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `0`. -/
/-
**SSet.horn₃₁.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `0`.
-/
abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 0 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `2`. -/
/-
**SSet.horn₃₁.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `2`.
-/
abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 2 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `3`. -/
/-
**SSet.horn₃₁.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `3`.
-/
abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂)
  (h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `desc`. -/
@[simps! pt]
/-
**SSet.horn₃₁.desc.multicofork** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn₃₁.desc`。
形式化陈述：{X : _root_.SSet} →   (f₀ f₂ f₃ : SSet.stdSimplex.obj { len := 2 } ⟶ X) → 
    CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ 2) f₀ =         Catego
ryTheory.CategoryStruct.comp (SSet.stdSimplex.δ 0) f₃ →       CategoryTheory.Cat
egoryStruct.comp (SSet.stdSimplex.δ 1) f₀ =           CategoryTheory.CategoryStr
uct.comp (SSet.stdSimplex.δ 0) f₂ →         CategoryTheory.CategoryStruct.comp (
SSet.stdSimplex.δ 2) f₂ =             CategoryTheory.CategoryStruct.comp (SSet.s
tdSimplex.δ 2) f₃ →           CategoryTheory.Limits.Multicofork             ((Co
mpleteLattice.MulticoequalizerDiagram.multispanIndex ⋯).toLinearOrder.map SSet.S
ubcomplex.toSSetFunctor)
参数：f₀ f₂ f₃ : SSet.stdSimplex.obj { len := 2 } ⟶ X；SSet.stdSimplex.δ 2；SSet.stdS
implex.δ 0；SSet.stdSimplex.δ 1；SSet.stdSimplex.δ 0；SSet.stdSimplex.δ 2；SSet.stdS
implex.δ 2；(CompleteLattice.MulticoequalizerDiagram.multispanIndex ⋯).toLinearOr
der.map SSet.Subcomplex.toSSetFunctor。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `desc`.
-/
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (1 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => False.elim (by simp at hi)
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x ↦ by
      dsimp at x ⊢
      fin_cases x
      · simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 3 (by simp)).hom,
          ← Category.assoc]
        convert! h₁₃ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← Category.assoc]
        convert! h₁₂ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 1 (by simp)).hom,
          ← Category.assoc]
        convert! h₂₃ <;> decide)

@[simp, reassoc]
/-
**SSet.horn₃₁.desc.multicofork_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc.multicofork_π_zero :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨0, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀ := rfl

@[simp, reassoc]
/-
**SSet.horn₃₁.desc.multicofork_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc.multicofork_π_two :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨2, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂ := rfl

@[simp, reassoc]
/-
**SSet.horn₃₁.desc.multicofork_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc.multicofork_π_three :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨3, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃ := rfl

/-- The morphism `Λ[3, 1] ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`. -/
/-
**SSet.horn₃₁.desc** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn₃₁`。
形式化陈述：desc : (Λ[3, 1] : SSet) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Λ[3, 1] ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`.
-/
noncomputable def desc : (Λ[3, 1] : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]
/-
**SSet.horn₃₁.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
/-
**SSet.horn₃₁.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 2).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]
/-
**SSet.horn₃₁.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in
/-
**SSet.horn₃₁.exists_desc** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₁`。
形式化陈述：exists_desc : exists (φ : (Λ[3, 1] : SSet) ⟶ X), ι₀ ≫ φ = f₀ ∧ ι₂ ≫ φ = f₂
 ∧ ι₃ ≫ φ = f₃
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.horn₃₁.ι₀_desc`：ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.horn₃₁.ι₂_desc`：ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂
· 使用引理 `SSet.horn₃₁.ι₃_desc`：ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma exists_desc : ∃ (φ : (Λ[3, 1] : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₂ ≫ φ = f₂ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩

end horn₃₁

namespace horn₃₂

/-- The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `0`. -/
/-
**SSet.horn₃₂.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `0`.
-/
abbrev ι₀ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 0 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `1`. -/
/-
**SSet.horn₃₂.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `1`.
-/
abbrev ι₁ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 1 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `3`. -/
/-
**SSet.horn₃₂.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `3`.
-/
abbrev ι₃ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 3 (by simp)

variable {X : SSet.{u}} (f₀ f₁ f₃ : Δ[2] ⟶ X)
  (h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `desc`. -/
@[simps! pt]
/-
**SSet.horn₃₂.desc.multicofork** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn₃₂.desc`。
形式化陈述：{X : _root_.SSet} →   (f₀ f₁ f₃ : SSet.stdSimplex.obj { len := 2 } ⟶ X) → 
    CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ 2) f₁ =         Catego
ryTheory.CategoryStruct.comp (SSet.stdSimplex.δ 1) f₃ →       CategoryTheory.Cat
egoryStruct.comp (SSet.stdSimplex.δ 2) f₀ =           CategoryTheory.CategoryStr
uct.comp (SSet.stdSimplex.δ 0) f₃ →         CategoryTheory.CategoryStruct.comp (
SSet.stdSimplex.δ 0) f₀ =             CategoryTheory.CategoryStruct.comp (SSet.s
tdSimplex.δ 0) f₁ →           CategoryTheory.Limits.Multicofork             ((Co
mpleteLattice.MulticoequalizerDiagram.multispanIndex ⋯).toLinearOrder.map SSet.S
ubcomplex.toSSetFunctor)
参数：f₀ f₁ f₃ : SSet.stdSimplex.obj { len := 2 } ⟶ X；SSet.stdSimplex.δ 2；SSet.stdS
implex.δ 1；SSet.stdSimplex.δ 2；SSet.stdSimplex.δ 0；SSet.stdSimplex.δ 0；SSet.stdS
implex.δ 0；(CompleteLattice.MulticoequalizerDiagram.multispanIndex ⋯).toLinearOr
der.map SSet.Subcomplex.toSSetFunctor。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `desc`.
-/
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (2 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => False.elim (by simp at hi)
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x ↦ by
      dsimp at x ⊢
      fin_cases x
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 2 3 (by simp)).hom,
          ← Category.assoc]
        convert! h₂₃ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← Category.assoc]
        convert! h₁₂ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 2 (by simp)).hom,
          ← Category.assoc]
        convert! h₀₂ <;> decide)

@[simp, reassoc]
/-
**SSet.horn₃₂.desc.multicofork_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc.multicofork_π_zero :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨0, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀ := rfl

@[simp, reassoc]
/-
**SSet.horn₃₂.desc.multicofork_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc.multicofork_π_one :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨1, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁ := rfl

@[simp, reassoc]
/-
**SSet.horn₃₂.desc.multicofork_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc.multicofork_π_three :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨3, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃ := rfl

/-- The morphism `Λ[3, 2] ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`. -/
/-
**SSet.horn₃₂.desc** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn₃₂`。
形式化陈述：desc : (Λ[3, 2] : SSet) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Λ[3, 2] ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`.
-/
noncomputable def desc : (Λ[3, 2] : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]
/-
**SSet.horn₃₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_desc : ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
/-
**SSet.horn₃₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_desc : ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 1).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]
/-
**SSet.horn₃₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₃_desc : ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in
/-
**SSet.horn₃₂.exists_desc** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn₃₂`。
形式化陈述：exists_desc : exists (φ : (Λ[3, 2] : SSet) ⟶ X), ι₀ ≫ φ = f₀ ∧ ι₁ ≫ φ = f₁
 ∧ ι₃ ≫ φ = f₃
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.horn₃₂.ι₀_desc`：ι₀_desc : ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.horn₃₂.ι₁_desc`：ι₁_desc : ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁
· 使用引理 `SSet.horn₃₂.ι₃_desc`：ι₃_desc : ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma exists_desc : ∃ (φ : (Λ[3, 2] : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₁ ≫ φ = f₁ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩

end horn₃₂

end SSet

